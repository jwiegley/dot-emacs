module CertCmd where
import PFE_Certs(CertType,QCertName(..))
import PrettyPrint(Printable(..),pp)

data CertCmd
   = ValidateCert QCertName
   | RemoveCert QCertName
   | NewCert CertType QCertName String
   | NewCertAll CertType String{-ModuleName-}
   | TodoCert
   deriving (Eq,Show)

instance Printable CertCmd where ppi = ppi . shellCmd

--isValidate ValidateCert{} = True
--isValidate _ = False

cmdCert (ValidateCert cert) = Just cert
cmdCert (RemoveCert cert) = Just cert
cmdCert (NewCert ty cert concl) = Just cert
cmdCert _ = Nothing

shellCmd (ValidateCert cert) = "cert validate "++quote (ppqcert cert)
shellCmd (RemoveCert cert) = "cert rm "++quote (ppqcert cert)
shellCmd (NewCert ty cert concl) =
    unwords ["cert new",ty,quote (ppqcert cert),quote concl]
shellCmd (NewCertAll ty mod) = unwords ["cert new -all",ty,mod]
shellCmd TodoCert = "cert todo"

ppqcert (QCertName m c) = pp m++"/"++c

quote s = q++s++q where q="\""
