module Main(main) where
import GHC
import CoreSyn
import qualified CoreUtils
import qualified Var
import qualified Type
import qualified TyCon
import qualified DataCon
import qualified Maybe
import qualified Module
import qualified Control.Monad.State as State
import Name
import Data.Generics
import NameEnv ( lookupNameEnv )
import HscTypes ( cm_binds, cm_types )
import MonadUtils ( liftIO )
import Outputable ( showSDoc, ppr )
import GHC.Paths ( libdir )
import DynFlags ( defaultDynFlags )
import List ( find )
-- The following modules come from the ForSyDe project. They are really
-- internal modules, so ForSyDe.cabal has to be modified prior to installing
-- ForSyDe to get access to these modules.
import qualified ForSyDe.Backend.VHDL.AST as AST
import qualified ForSyDe.Backend.VHDL.Ppr
import qualified ForSyDe.Backend.Ppr
-- This is needed for rendering the pretty printed VHDL
import Text.PrettyPrint.HughesPJ (render)

main = 
		do
			defaultErrorHandler defaultDynFlags $ do
				runGhc (Just libdir) $ do
					dflags <- getSessionDynFlags
					setSessionDynFlags dflags
					--target <- guessTarget "adder.hs" Nothing
					--liftIO (print (showSDoc (ppr (target))))
					--liftIO $ printTarget target
					--setTargets [target]
					--load LoadAllTargets
					--core <- GHC.compileToCoreSimplified "Adders.hs"
					core <- GHC.compileToCoreSimplified "Adders.hs"
					liftIO $ printBinds (cm_binds core)
					let bind = findBind "half_adder" (cm_binds core)
					let NonRec var expr = bind
					let sess = State.execState (do {(name, f) <- mkHWFunction bind; addFunc name f}) (VHDLSession 0 builtin_funcs)
					liftIO $ putStr $ showSDoc $ ppr expr
					liftIO $ putStr "\n\n"
					liftIO $ putStr $ render $ ForSyDe.Backend.Ppr.ppr $ getArchitecture sess bind
					return expr

printTarget (Target (TargetFile file (Just x)) obj Nothing) =
	print $ show file

printBinds [] = putStr "done\n\n"
printBinds (b:bs) = do
	printBind b
	putStr "\n"
	printBinds bs

printBind (NonRec b expr) = do
	putStr "NonRec: "
	printBind' (b, expr)

printBind (Rec binds) = do
	putStr "Rec: \n"	
	foldl1 (>>) (map printBind' binds)

printBind' (b, expr) = do
	putStr $ getOccString b
	--putStr $ showSDoc $ ppr expr
	putStr "\n"

findBind :: String -> [CoreBind] -> CoreBind
findBind lookfor =
	-- This ignores Recs and compares the name of the bind with lookfor,
	-- disregarding any namespaces in OccName and extra attributes in Name and
	-- Var.
	Maybe.fromJust . find (\b -> case b of 
		Rec l -> False
		NonRec var _ -> lookfor == (occNameString $ nameOccName $ getName var)
	)

-- Accepts a port name and an argument to map to it.
-- Returns the appropriate line for in the port map
getPortMapEntry binds (Port portname) (Var id) = 
	(Just (AST.unsafeVHDLBasicId portname)) AST.:=>: (AST.ADName (AST.NSimple (AST.unsafeVHDLBasicId signalname)))
	where
		Port signalname = Maybe.fromMaybe
			(error $ "Argument " ++ getOccString id ++ "is unknown")
			(lookup id binds)

getPortMapEntry binds _ a = error $ "Unsupported argument: " ++ (showSDoc $ ppr a)

getInstantiations ::
	VHDLSession
	-> [PortNameMap]             -- The arguments that need to be applied to the
															 -- expression.
	-> PortNameMap               -- The output ports that the expression should generate.
	-> [(CoreBndr, PortNameMap)] -- A list of bindings in effect
	-> CoreSyn.CoreExpr          -- The expression to generate an architecture for
	-> [AST.ConcSm]              -- The resulting VHDL code

-- A lambda expression binds the first argument (a) to the binder b.
getInstantiations sess (a:as) outs binds (Lam b expr) =
	getInstantiations sess as outs ((b, a):binds) expr

-- A case expression that checks a single variable and has a single
-- alternative, can be used to take tuples apart
getInstantiations sess args outs binds (Case (Var v) b _ [res]) =
	case altcon of
		DataAlt datacon ->
			if (DataCon.isTupleCon datacon) then
				getInstantiations sess args outs binds' expr
			else
				error "Data constructors other than tuples not supported"
		otherwise ->
			error "Case binders other than tuples not supported"
	where
		binds' = (zip bind_vars tuple_ports) ++ binds
		(altcon, bind_vars, expr) = res
		-- Find the portnamemaps for each of the tuple's elements
		Tuple tuple_ports = Maybe.fromMaybe 
			(error $ "Case expression uses unknown scrutinee " ++ getOccString v)
			(lookup v binds)

-- An application is an instantiation of a component
getInstantiations sess args outs binds app@(App expr arg) =
	if isTupleConstructor f then
		let
			Tuple outports = outs
			(tys, vals) = splitTupleConstructorArgs fargs
		in
			concat $ zipWith 
				(\outs' expr' -> getInstantiations sess args outs' binds expr')
				outports vals
	else
		[AST.CSISm comp]
	where
		((Var f), fargs) = collectArgs app
		comp = AST.CompInsSm
			(AST.unsafeVHDLBasicId "app")
			(AST.IUEntity (AST.NSimple (AST.unsafeVHDLBasicId compname)))
			(AST.PMapAspect ports)
		compname = getOccString f
		hwfunc = Maybe.fromMaybe
			(error $ "Function " ++ compname ++ "is unknown")
			(lookup compname (funcs sess))
		HWFunction inports outport = hwfunc
		ports = 
			zipWith (getPortMapEntry binds) inports fargs
		  ++ mapOutputPorts outport outs

getInstantiations sess args outs binds expr = 
	error $ "Unsupported expression" ++ (showSDoc $ ppr $ expr)

-- Is the given name a (binary) tuple constructor
isTupleConstructor :: Var.Var -> Bool
isTupleConstructor var =
	Name.isWiredInName name
	&& Name.nameModule name == tuple_mod
	&& (Name.occNameString $ Name.nameOccName name) == "(,)"
	where
		name = Var.varName var
		mod = nameModule name
		tuple_mod = Module.mkModule (Module.stringToPackageId "ghc-prim") (Module.mkModuleName "GHC.Tuple")

-- Split arguments into type arguments and value arguments This is probably
-- not really sufficient (not sure if Types can actually occur as value
-- arguments...)
splitTupleConstructorArgs :: [CoreExpr] -> ([CoreExpr], [CoreExpr])
splitTupleConstructorArgs (e:es) =
	case e of
		Type t     -> (e:tys, vals)
		otherwise  -> (tys, e:vals)
	where
		(tys, vals) = splitTupleConstructorArgs es

mapOutputPorts ::
	PortNameMap         -- The output portnames of the component
	-> PortNameMap      -- The output portnames and/or signals to map these to
	-> [AST.AssocElem]  -- The resulting output ports

-- Map the output port of a component to the output port of the containing
-- entity.
mapOutputPorts (Port portname) (Port signalname) =
	[(Just (AST.unsafeVHDLBasicId portname)) AST.:=>: (AST.ADName (AST.NSimple (AST.unsafeVHDLBasicId signalname)))]

-- Map matching output ports in the tuple
mapOutputPorts (Tuple ports) (Tuple signals) =
	concat (zipWith mapOutputPorts ports signals)

getArchitecture ::
	VHDLSession
	-> CoreBind               -- The binder to expand into an architecture
	-> AST.ArchBody           -- The resulting architecture
	 
getArchitecture sess (Rec _) = error "Recursive binders not supported"

getArchitecture sess (NonRec var expr) =
	AST.ArchBody
		(AST.unsafeVHDLBasicId "structural")
		-- Use unsafe for now, to prevent pulling in ForSyDe error handling
		(AST.NSimple (AST.unsafeVHDLBasicId name))
		[]
		(getInstantiations sess inports outport [] expr)
	where
		name = (getOccString var)
		hwfunc = Maybe.fromMaybe
			(error $ "Function " ++ name ++ "is unknown? This should not happen!")
			(lookup name (funcs sess))
		HWFunction inports outport = hwfunc

data PortNameMap =
	Tuple [PortNameMap]
	| Port  String
  deriving (Show)

-- Generate a port name map (or multiple for tuple types) in the given direction for
-- each type given.
getPortNameMapForTys :: String -> Int -> [Type] -> [PortNameMap]
getPortNameMapForTys prefix num [] = [] 
getPortNameMapForTys prefix num (t:ts) =
	(getPortNameMapForTy (prefix ++ show num) t) : getPortNameMapForTys prefix (num + 1) ts

getPortNameMapForTy	:: String -> Type -> PortNameMap
getPortNameMapForTy name ty =
	if (TyCon.isTupleTyCon tycon) then
		-- Expand tuples we find
		Tuple (getPortNameMapForTys name 0 args)
	else -- Assume it's a type constructor application, ie simple data type
		-- TODO: Add type?
		Port name
	where
		(tycon, args) = Type.splitTyConApp ty 

data HWFunction = HWFunction { -- A function that is available in hardware
	inPorts   :: [PortNameMap],
	outPort   :: PortNameMap
	--entity    :: AST.EntityDec
} deriving (Show)

-- Turns a CoreExpr describing a function into a description of its input and
-- output ports.
mkHWFunction ::
	CoreBind                                   -- The core binder to generate the interface for
	-> VHDLState (String, HWFunction)          -- The name of the function and its interface

mkHWFunction (NonRec var expr) =
		return (name, HWFunction inports outport)
	where
		name = (getOccString var)
		ty = CoreUtils.exprType expr
		(fargs, res) = Type.splitFunTys ty
		args = if length fargs == 1 then fargs else (init fargs)
		--state = if length fargs == 1 then () else (last fargs)
		inports = case args of
			-- Handle a single port specially, to prevent an extra 0 in the name
			[port] -> [getPortNameMapForTy "portin" port]
			ps     -> getPortNameMapForTys "portin" 0 ps
		outport = getPortNameMapForTy "portout" res

mkHWFunction (Rec _) =
	error "Recursive binders not supported"

data VHDLSession = VHDLSession {
	nameCount :: Int,                      -- A counter that can be used to generate unique names
	funcs     :: [(String, HWFunction)]    -- All functions available, indexed by name
} deriving (Show)

type VHDLState = State.State VHDLSession

-- Add the function to the session
addFunc :: String -> HWFunction -> VHDLState ()
addFunc name f = do
	fs <- State.gets funcs -- Get the funcs element form the session
	State.modify (\x -> x {funcs = (name, f) : fs }) -- Prepend name and f

builtin_funcs = 
	[ 
		("hwxor", HWFunction [Port "a", Port "b"] (Port "o")),
		("hwand", HWFunction [Port "a", Port "b"] (Port "o"))
	]
