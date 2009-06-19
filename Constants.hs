module Constants where
  
import qualified ForSyDe.Backend.VHDL.AST as AST

--------------
-- Identifiers
--------------

-- | reset and clock signal identifiers in String form
resetStr, clockStr :: String
resetStr = "resetn"
clockStr = "clock"

-- | reset and clock signal identifiers in basic AST.VHDLId form
resetId, clockId :: AST.VHDLId
resetId = AST.unsafeVHDLBasicId resetStr
clockId = AST.unsafeVHDLBasicId clockStr


-- | \"types\" identifier
typesId :: AST.VHDLId
typesId = AST.unsafeVHDLBasicId "types"

-- | work identifier
workId :: AST.VHDLId
workId = AST.unsafeVHDLBasicId "work"

-- | std identifier
stdId :: AST.VHDLId
stdId = AST.unsafeVHDLBasicId "std"


-- | textio identifier
textioId :: AST.VHDLId
textioId = AST.unsafeVHDLBasicId "textio"

-- | range attribute identifier
rangeId :: AST.VHDLId
rangeId = AST.unsafeVHDLBasicId "range"


-- | range attribute identifier
imageId :: AST.VHDLId
imageId = AST.unsafeVHDLBasicId "image"

-- | event attribute identifie
eventId :: AST.VHDLId
eventId = AST.unsafeVHDLBasicId "event"


-- | default function identifier
defaultId :: AST.VHDLId
defaultId = AST.unsafeVHDLBasicId "default"

-- FSVec function identifiers

-- | ex (operator ! in original Haskell source) function identifier
exId :: AST.VHDLId
exId = AST.unsafeVHDLBasicId "ex"

-- | sel (function select in original Haskell source) function identifier
selId :: AST.VHDLId
selId = AST.unsafeVHDLBasicId "sel"


-- | ltplus (function (<+) in original Haskell source) function identifier
ltplusId :: AST.VHDLId
ltplusId = AST.unsafeVHDLBasicId "ltplus"


-- | plusplus (function (++) in original Haskell source) function identifier
plusplusId :: AST.VHDLId
plusplusId = AST.unsafeVHDLBasicId "plusplus"


-- | empty function identifier
emptyId :: AST.VHDLId
emptyId = AST.unsafeVHDLBasicId "empty"

-- | plusgt (function (+>) in original Haskell source) function identifier
plusgtId :: AST.VHDLId
plusgtId = AST.unsafeVHDLBasicId "plusgt"

-- | singleton function identifier
singletonId :: AST.VHDLId
singletonId = AST.unsafeVHDLBasicId "singleton"

-- | length function identifier
lengthId :: AST.VHDLId
lengthId = AST.unsafeVHDLBasicId "length"


-- | isnull (function null in original Haskell source) function identifier
isnullId :: AST.VHDLId
isnullId = AST.unsafeVHDLBasicId "isnull"


-- | replace function identifier
replaceId :: AST.VHDLId
replaceId = AST.unsafeVHDLBasicId "replace"


-- | head function identifier
headId :: AST.VHDLId
headId = AST.unsafeVHDLBasicId "head"


-- | last function identifier
lastId :: AST.VHDLId
lastId = AST.unsafeVHDLBasicId "last"


-- | init function identifier
initId :: AST.VHDLId
initId = AST.unsafeVHDLBasicId "init"


-- | tail function identifier
tailId :: AST.VHDLId
tailId = AST.unsafeVHDLBasicId "tail"


-- | take function identifier
takeId :: AST.VHDLId
takeId = AST.unsafeVHDLBasicId "take"


-- | drop function identifier
dropId :: AST.VHDLId
dropId = AST.unsafeVHDLBasicId "drop"

-- | shiftl function identifier
shiftlId :: AST.VHDLId
shiftlId = AST.unsafeVHDLBasicId "shiftl"

-- | shiftr function identifier
shiftrId :: AST.VHDLId
shiftrId = AST.unsafeVHDLBasicId "shiftr"

-- | rotl function identifier
rotlId :: AST.VHDLId
rotlId = AST.unsafeVHDLBasicId "rotl"

-- | reverse function identifier
rotrId :: AST.VHDLId
rotrId = AST.unsafeVHDLBasicId "rotr"

-- | reverse function identifier
reverseId :: AST.VHDLId
reverseId = AST.unsafeVHDLBasicId "reverse"

-- | copy function identifier
copyId :: AST.VHDLId
copyId = AST.unsafeVHDLBasicId "copy"

------------------
-- VHDL type marks
------------------

-- | Stardard logic type mark
std_logicTM :: AST.TypeMark
std_logicTM = AST.unsafeVHDLBasicId "std_logic"

-- | boolean type mark
booleanTM :: AST.TypeMark
booleanTM = AST.unsafeVHDLBasicId "boolean"

-- | fsvec_index AST. TypeMark
tfvec_indexTM :: AST.TypeMark
tfvec_indexTM = AST.unsafeVHDLBasicId "tfvec_index"

-- | natural AST. TypeMark
naturalTM :: AST.TypeMark
naturalTM = AST.unsafeVHDLBasicId "natural"