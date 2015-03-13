module OldSyntaxRec where
import SyntaxRec

-- For backward compatibility:
type HsPat = HsPatI HsName
type HsType = HsTypeI HsName
type HsExp  = HsExpI HsName
type HsDecl = HsDeclI HsName
type HsModuleR = HsModuleRI HsName

type BaseDecl = BaseDeclI HsName
type BaseExp  = BaseExpI  HsName
type BasePat  = BasePatI  HsName
type BaseType = BaseTypeI HsName

type HsModuleRI i = HsModuleI i [HsDeclI i]

type HsStmtR   = HsStmt HsExp HsPat [HsDecl]
type HsAltR    = HsAlt HsExp HsPat [HsDecl]
