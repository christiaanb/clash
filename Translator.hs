module Main(main) where
import GHC
import CoreSyn
import qualified CoreUtils
import qualified Var
import qualified Type
import qualified TyCon
import qualified DataCon
import qualified Maybe
import Name
import Data.Generics
import NameEnv ( lookupNameEnv )
import HscTypes ( cm_binds, cm_types )
import MonadUtils ( liftIO )
import Outputable ( showSDoc, ppr )
import GHC.Paths ( libdir )
import DynFlags ( defaultDynFlags )
import List ( find )

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
					let bind = findBind "no_carry_adder" (cm_binds core)
					let NonRec var expr = bind
					liftIO $ putStr $ showSDoc $ ppr expr
					liftIO $ putStr "\n\n"
					liftIO $ putStr $ getEntity bind
					liftIO $ putStr $ getArchitecture bind
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

-- Generate a port (or multiple for tuple types) in the given direction for
-- each type given.
getPortsForTys :: String -> String -> Int -> [Type] -> String
getPortsForTys dir prefix num [] = ""
getPortsForTys dir prefix num (t:ts) = 
	(getPortsForTy dir (prefix ++ show num) t) ++ getPortsForTys dir prefix (num + 1) ts

getPortsForFunTy ty =
		-- All of a function's arguments become IN ports, the result becomes on
		-- (or more) OUT ports.
		-- Drop the first ;\n
		drop 2 (getPortsForTys "in" "portin" 0 args) ++ (getPortsForTy "out" "portout" res) ++ "\n"
	where
		(args, res) = Type.splitFunTys ty

getPortsForTy	:: String -> String -> Type -> String
getPortsForTy dir name ty =
	if (TyCon.isTupleTyCon tycon) then
		-- Expand tuples we find
		getPortsForTys dir name 0 args
	else -- Assume it's a type constructor application, ie simple data type
		let 
			vhdlTy = showSDoc $ ppr $ TyCon.tyConName tycon;
		in
			";\n\t" ++ name ++ " : " ++ dir ++ " " ++ vhdlTy
	where
		(tycon, args) = Type.splitTyConApp ty 

getEntity (NonRec var expr) =
		"entity " ++ name ++ " is\n"
		++ "port (\n"
		++ getPortsForFunTy ty
	  ++ ");\n"
		++ "end " ++ name ++ ";\n\n"
	where
		name = (getOccString var)
		ty = CoreUtils.exprType expr

-- Accepts a port name and an argument to map to it.
-- Returns the appropriate line for in the port map
getPortMapEntry binds portname (Var id) = 
	"\t" ++ portname ++ " => " ++ signalname ++ "\n"
	where
		Port signalname = Maybe.fromMaybe
			(error $ "Argument " ++ getOccString id ++ "is unknown")
			(lookup id binds)

getPortMapEntry binds _ a = error $ "Unsupported argument: " ++ (showSDoc $ ppr a)

getInstantiations ::
	PortNameMap                  -- The arguments that need to be applied to the
															 -- expression. Should always be the Args
															 -- constructor.
	-> [(CoreBndr, PortNameMap)] -- A list of bindings in effect
	-> CoreSyn.CoreExpr          -- The expression to generate an architecture for
	-> String                    -- The resulting VHDL code

-- A lambda expression binds the first argument (a) to the binder b.
getInstantiations (Args (a:as)) binds (Lam b expr) =
	getInstantiations (Args as) ((b, a):binds) expr

-- A case expression that checks a single variable and has a single
-- alternative, can be used to take tuples apart
getInstantiations args binds (Case (Var v) b _ [res]) =
	case altcon of
		DataAlt datacon ->
			if (DataCon.isTupleCon datacon) then
				getInstantiations args binds' expr
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
getInstantiations args binds app@(App expr arg) =
	--indent ++ "F:\n" ++ (getInstantiations (' ':indent) expr) ++ "\n" ++ indent ++ "A:\n" ++ (getInstantiations (' ':indent) arg) ++ "\n"
	"app : " ++ (getOccString f) ++ "\n"
	++ "port map (\n"
	++ concat (zipWith (getPortMapEntry binds) ["portin0", "portin1"] args)
	++ ");\n"
	where
		((Var f), args) = collectArgs app

getInstantiations args binds expr = showSDoc $ ppr $ expr

getArchitecture (NonRec var expr) =
	"architecture structural of " ++ name ++ " is\n"
	++ "begin\n"
	++ getInstantiations (Args inportnames) [] expr
	++ "end structural\n"
	where
		name = (getOccString var)
		ty = CoreUtils.exprType expr
		(fargs, res) = Type.splitFunTys ty
		--state = if length fargs == 1 then () else (last fargs)
		ports = if length fargs == 1 then fargs else (init fargs)
		inportnames = case ports of
			[port] -> [getPortNameMapForTy "portin" port]
			ps     -> getPortNameMapForTys "portin" 0 ps

data PortNameMap =
	Args [PortNameMap] -- Each of the submaps represent an argument to the
	                   -- function. Should only occur at top level.
	| Tuple [PortNameMap]
	| Port  String

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
