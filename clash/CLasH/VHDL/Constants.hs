module CLasH.VHDL.Constants where

-- VHDL Imports  
import qualified Language.VHDL.AST as AST

-- | A list of all builtin functions. Partly duplicates the name table
-- in VHDL.Generate, but we can't use that map everywhere due to
-- circular dependencie.
builtinIds = [ exId, replaceId, headId, lastId, tailId, initId, takeId, dropId
             , selId, plusgtId, ltplusId, plusplusId, mapId, zipWithId, foldlId
             , foldrId, zipId, unzipId, shiftIntoLId, shiftIntoRId, rotlId, rotrId
             , concatId, reverseId, iteratenId, iterateId, generatenId, generateId
             , emptyId, singletonId, copynId, copyId, lengthTId, nullId
             , hwxorId, hwandId, hworId, hwnotId, equalityId, inEqualityId, ltId
             , lteqId, gtId, gteqId, boolOrId, boolAndId, plusId, timesId
             , negateId, minusId, fromSizedWordId, fromIntegerId, resizeWordId
             , resizeIntId, sizedIntId, smallIntegerId, fstId, sndId, blockRAMId
             , splitId, minimumId, fromRangedWordId, xorId, shiftLId , shiftRId
             , u2bvId, s2bvId, bv2sId, bv2uId, maxIndexId
             ]
--------------
-- Identifiers
--------------

u2bvId, s2bvId, bv2sId, bv2uId :: String
u2bvId = "u2bv"
s2bvId = "s2bv"
bv2sId = "bv2s"
bv2uId = "bv2u"

maxIndexId :: String
maxIndexId = "maxIndex"

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
selId = "vselect"


-- | ltplus (function (<+) in original Haskell source) function identifier
ltplusId :: String
ltplusId = "<+"


-- | plusplus (function (++) in original Haskell source) function identifier
plusplusId :: String
plusplusId = "<++>"


-- | empty function identifier
emptyId :: String
emptyId = "empty"

-- | plusgt (function (+>) in original Haskell source) function identifier
plusgtId :: String
plusgtId = "+>"

-- | singleton function identifier
singletonId :: String
singletonId = "singleton"

-- | length attribute identifier
lengthId :: String
lengthId = "length"


-- | isnull (function null in original Haskell source) function identifier
nullId :: String
nullId = "vnull"


-- | replace function identifier
replaceId :: String
replaceId = "vreplace"


-- | head function identifier
headId :: String
headId = "vhead"


-- | last function identifier
lastId :: String
lastId = "vlast"


-- | init function identifier
initId :: String
initId = "vinit"


-- | tail function identifier
tailId :: String
tailId = "vtail"

-- | minimum ftp function identifier
minimumId :: String
minimumId = "minimum"

-- | take function identifier
takeId :: String
takeId = "vtake"


-- | drop function identifier
dropId :: String
dropId = "vdrop"

-- | shiftl function identifier
shiftIntoLId :: String
shiftIntoLId = "+>>"

-- | shiftr function identifier
shiftIntoRId :: String
shiftIntoRId = "<<+"

-- | rotl function identifier
rotlId :: String
rotlId = "vrotl"

-- | reverse function identifier
rotrId :: String
rotrId = "vrotr"

-- | concatenate the vectors in a vector
concatId :: String
concatId = "vconcat"

-- | reverse function identifier
reverseId :: String
reverseId = "vreverse"

-- | iterate function identifier
iterateId :: String
iterateId = "viterate"

-- | iteraten function identifier
iteratenId :: String
iteratenId = "viteraten"

-- | iterate function identifier
generateId :: String
generateId = "vgenerate"

-- | iteraten function identifier
generatenId :: String
generatenId = "vgeneraten"

-- | copy function identifier
copyId :: String
copyId = "vcopy"

-- | copyn function identifier
copynId :: String
copynId = "vcopyn"

-- | map function identifier
mapId :: String
mapId = "vmap"

-- | zipwith function identifier
zipWithId :: String
zipWithId = "vzipWith"

-- | foldl function identifier
foldlId :: String
foldlId = "vfoldl"

-- | foldr function identifier
foldrId :: String
foldrId = "vfoldr"

-- | zip function identifier
zipId :: String
zipId = "vzip"

-- | unzip function identifier
unzipId :: String
unzipId = "vunzip"

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

xorId :: String
xorId = "xor"

shiftLId :: String
shiftLId = "shiftL"

shiftRId :: String
shiftRId = "shiftR"

lengthTId :: String
lengthTId = "vlengthT"

fstId :: String
fstId = "fst"

sndId :: String
sndId = "snd"

splitId :: String
splitId = "vsplit"

-- Equality Operations
equalityId :: String
equalityId = "=="

inEqualityId :: String
inEqualityId = "/="

gtId :: String
gtId = ">"

ltId :: String
ltId = "<"

gteqId :: String
gteqId = ">="

lteqId :: String
lteqId = "<="

boolOrId :: String
boolOrId = "||"

boolAndId :: String
boolAndId = "&&"

boolNot :: String
boolNot = "not"

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
fromSizedWordId = "fromUnsigned"

fromRangedWordId :: String
fromRangedWordId = "fromIndex"

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

resizeWordId :: String
resizeWordId = "resizeUnsigned"

resizeIntId :: String
resizeIntId = "resizeSigned"

smallIntegerId :: String
smallIntegerId = "smallInteger"

sizedIntId :: String
sizedIntId = "Signed"

tfvecId :: String
tfvecId = "Vector"

blockRAMId :: String
blockRAMId = "blockRAM"

-- | output file identifier (from std.textio)
showIdString :: String
showIdString = "show"

showId :: AST.VHDLId
showId = AST.unsafeVHDLBasicId showIdString

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
