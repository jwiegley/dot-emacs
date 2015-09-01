-- Labelled fields, used in patterns and expressions
module HsFieldsMaps where
import HsFieldsStruct
import MUtils
import AccList(accList)

--------------------------------------------------------------------------------
accFieldsI vf ef = accList (accFieldI vf ef)
accFieldI vf ef (HsField fnm e)    = vf fnm . ef e -- hmm, vf fnm

mapFieldsI vf ef = map (mapFieldI vf ef)
mapFieldI vf ef (HsField nm e) = HsField (vf nm) (ef e) -- hmm

seqFieldsI fs = mapM seqFieldI fs
seqFieldI (HsField nm e) = HsField # nm <# e
