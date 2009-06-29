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


-- | high attribute identifier
highId :: AST.VHDLId
highId = AST.unsafeVHDLBasicId "high"

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
exId :: String
exId = "!"

-- | sel (function select in original Haskell source) function identifier
selId :: String
selId = "select"


-- | ltplus (function (<+) in original Haskell source) function identifier
ltplusId :: String
ltplusId = "<+"


-- | plusplus (function (++) in original Haskell source) function identifier
plusplusId :: String
plusplusId = "++"


-- | empty function identifier
emptyId :: String
emptyId = "empty"

-- | plusgt (function (+>) in original Haskell source) function identifier
plusgtId :: String
plusgtId = "+>"

-- | singleton function identifier
singletonId :: String
singletonId = "singleton"

-- | length function identifier
lengthId :: String
lengthId = "length"


-- | isnull (function null in original Haskell source) function identifier
isnullId :: String
isnullId = "isnull"


-- | replace function identifier
replaceId :: String
replaceId = "replace"


-- | head function identifier
headId :: String
headId = "head"


-- | last function identifier
lastId :: String
lastId = "last"


-- | init function identifier
initId :: String
initId = "init"


-- | tail function identifier
tailId :: String
tailId = "tail"


-- | take function identifier
takeId :: String
takeId = "take"


-- | drop function identifier
dropId :: String
dropId = "drop"

-- | shiftl function identifier
shiftlId :: String
shiftlId = "shiftl"

-- | shiftr function identifier
shiftrId :: String
shiftrId = "shiftr"

-- | rotl function identifier
rotlId :: String
rotlId = "rotl"

-- | reverse function identifier
rotrId :: String
rotrId = "rotr"

-- | reverse function identifier
reverseId :: String
reverseId = "reverse"

-- | copy function identifier
copyId :: String
copyId = "copy"

-- | map function identifier
mapId :: String
mapId = "map"

-- | zipwith function identifier
zipWithId :: String
zipWithId = "zipWith"

-- | foldl function identifier
foldlId :: String
foldlId = "foldl"

-- | foldr function identifier
foldrId :: String
foldrId = "foldr"

-- | zip function identifier
zipId :: String
zipId = "zip"

-- | unzip function identifier
unzipId :: String
unzipId = "unzip"

-- | hwxor function identifier
hwxorId :: String
hwxorId = "hwxor"

-- | hwor function identifier
hworId :: String
hworId = "hwor"

-- | hwnot function identifier
hwnotId :: String
hwnotId = "hwnot"

-- | hwand function identifier
hwandId :: String
hwandId = "hwand"

lengthTId :: String
lengthTId = "lengthT"

------------------
-- VHDL type marks
------------------

-- | The Bit type mark
bitTM :: AST.TypeMark
bitTM = AST.unsafeVHDLBasicId "Bit"

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

-- | integer TypeMark
integerTM :: AST.TypeMark
integerTM = AST.unsafeVHDLBasicId "integer"
