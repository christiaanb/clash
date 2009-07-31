module CLasH.VHDL.Constants where
  
import qualified Language.VHDL.AST as AST

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

integerId :: AST.VHDLId
integerId = AST.unsafeVHDLBasicId "integer"

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
nullId :: String
nullId = "null"


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

-- | concatenate the vectors in a vector
concatId :: String
concatId = "concat"

-- | reverse function identifier
reverseId :: String
reverseId = "reverse"

-- | iterate function identifier
iterateId :: String
iterateId = "iterate"

-- | iteraten function identifier
iteratenId :: String
iteratenId = "iteraten"

-- | iterate function identifier
generateId :: String
generateId = "generate"

-- | iteraten function identifier
generatenId :: String
generatenId = "generaten"

-- | copy function identifier
copyId :: String
copyId = "copy"

-- | copyn function identifier
copynId :: String
copynId = "copyn"

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

-- Numeric Operations

-- | plus operation identifier
plusId :: String
plusId = "+"

-- | times operation identifier
timesId :: String
timesId = "*"

-- | negate operation identifier
negateId :: String
negateId = "negate"

-- | minus operation identifier
minusId :: String
minusId = "-"

-- | convert sizedword to ranged
fromSizedWordId :: String
fromSizedWordId = "fromSizedWord"

toIntegerId :: String
toIntegerId = "to_integer"

fromIntegerId :: String
fromIntegerId = "fromInteger"

toSignedId :: String
toSignedId = "to_signed"

toUnsignedId :: String
toUnsignedId = "to_unsigned"

resizeId :: String
resizeId = "resize"

sizedIntId :: String
sizedIntId = "SizedInt"

tfvecId :: String
tfvecId = "TFVec"

-- | output file identifier (from std.textio)
showIdString :: String
showIdString = "show"

showId :: AST.VHDLId
showId = AST.unsafeVHDLExtId showIdString

-- | write function identifier (from std.textio)
writeId :: AST.VHDLId
writeId = AST.unsafeVHDLBasicId "write"

-- | output file identifier (from std.textio)
outputId :: AST.VHDLId
outputId = AST.unsafeVHDLBasicId "output"

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

-- | signed TypeMark
signedTM :: AST.TypeMark
signedTM = AST.unsafeVHDLBasicId "signed"

-- | unsigned TypeMark
unsignedTM :: AST.TypeMark
unsignedTM = AST.unsafeVHDLBasicId "unsigned"

-- | string TypeMark
stringTM :: AST.TypeMark
stringTM = AST.unsafeVHDLBasicId "string"

-- | tup VHDLName suffix
tupVHDLSuffix :: AST.VHDLId -> AST.Suffix
tupVHDLSuffix id = AST.SSimple id