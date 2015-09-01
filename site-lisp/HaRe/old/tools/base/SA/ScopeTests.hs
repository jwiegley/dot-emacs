
module ScopeTests

where
------------------------------------------------------------------------------
-- some tests

loc = SrcLoc "Scope tests" 0 0

names2 @ [fn,gn,hn,kn,xn,yn,zn] = map UnQual ["f","g","h","k","x","y","z"]
names3 @ [an,bn,cn,dn,en,tn,sn] = map UnQual ["A","B","C","D","E","T","S"]

exps @  [fe,ge,he,ke,xe,ye,ze] = map hsEVar  names2
pats @  [fp,gp,hp,kp,xp,yp,zp] = map hsPVar  names2
typs @  [ft,gt,ht,kt,xt,yt,zt] = map hsTyVar names2

cons @  [ac,bc,cc,dc,ec,tc,sc] = map hsECon  names3
tcons @ [at,bt,ct,dt,et,tt,st] = map hsTyCon names3

ap2 [x] = x
ap2 (x:y:xs) = ap2((hsApp x y):xs)

apt [x] = x
apt (x:y:xs) = apt((hsTyApp x y):xs)

arr = hsTyFun


class1 = hsClassDecl loc [] (apt [ct,xt])
           [ hsTypeSig loc [fn] [] (xt `arr` xt) ]
class2 = hsClassDecl loc [apt[ct,yt]] (apt [dt,yt])
           [ hsTypeSig loc [gn] [] (yt `arr` yt) ]
class3 = hsClassDecl loc [apt[at,yt,xt]] (apt [et,yt,yt])
           [ hsTypeSig loc [zn] [] (yt `arr` yt) ]         

inst0 = hsInstDecl loc [] (ct) []
inst0'= hsInstDecl loc [] (xt) []
inst1 = hsInstDecl loc [] (apt [ct,xt]) []
inst2 = hsInstDecl loc [] (apt [ct,apt [dt,xt,xt]]) []
inst3 = hsInstDecl loc [] (apt [ct,apt [dt,at]]) []
inst4 = hsInstDecl loc [apt [dt,xt]] (apt [ct,tt]) []
inst5 = hsInstDecl loc [] (apt [ct,at]) []
inst6 = hsInstDecl loc [] (yt `arr` yt) []

data1 = hsDataDecl loc [] [tt] [HsConDecl loc cn []] []
data2 = hsDataDecl loc [] [tt,xt] [] []
data3 = hsDataDecl loc [] [tt] [HsConDecl loc cn [HsBangedType yt]
                             ,HsConDecl loc dn [HsUnBangedType at]
                             ,HsConDecl loc dn []
                             ] []
data4 = hsDataDecl loc [] [tt,xt] [HsConDecl loc dn [HsUnBangedType st]] []
data5 = hsDataDecl loc [] [tt,xt] [HsConDecl loc dn [HsUnBangedType (apt [st,xt])]] []
data6 = hsDataDecl loc [] [tt,xt] [HsConDecl loc dn [HsUnBangedType (apt [st,xt,yt])]] []
data7 = hsDataDecl loc [] [tt,xt] [HsConDecl loc dn [HsUnBangedType (apt [st,xt,yt,yt])]] []

type1 = hsTypeDecl loc [st,xt,yt] (hsTyTuple [xt,yt])
sig1  = hsTypeSig loc [zn] [] (apt [st,xt])

p0 = [class1,class2,class3,inst1,inst2,inst3]
p1 = [inst2]
p2 = [class1,class1,data1,data2,inst4,inst5]


insts :: [(String, [HsDecl])]
insts = [ ("Ill formed instance type", [ hsInstDecl loc [] (ct) [] ] )
        , ("Ill formed instance type", [ hsInstDecl loc [] (xt) [] ])
        , ("Ill formed instance type", [hsInstDecl loc [] (apt [ct,xt]) []])
        , ("Undefined class & type" , [hsInstDecl loc [] (apt [ct,dt]) []])
        , ("Duplicate type vars", 
                [ hsDataDecl  loc [] [dt] [] []
                , hsClassDecl loc [] (apt [ct,xt]) []
                , hsInstDecl loc [] (apt [ct,apt [dt,xt,xt]]) []])
        , ("Argument to TyCon must be tyvar", [hsInstDecl loc [] (apt [ct,apt [dt,at]]) []])
        , ("Many undefined", [hsInstDecl loc [apt [dt,xt]] (apt [ct,tt]) []])
        , ("Type synonym illegal",   
                 [ hsTypeDecl  loc [at] bt
                 , hsDataDecl  loc [] [bt] [] []
                 , hsClassDecl loc [] (apt [ct,xt]) []
                 , hsInstDecl  loc [] (apt [ct,at]) []
                 ])
        , ("Context errors", 
                [ hsDataDecl  loc [] [at] [] []
                , hsDataDecl  loc [] [bt,xt] [] []
                , hsClassDecl loc [] (apt [ct,xt]) []
                , hsClassDecl loc [] (apt [dt,xt]) []
                , hsInstDecl  loc [xt] (apt [ct,at]) []
                , hsInstDecl  loc [dt] (apt [ct,at]) []
                , hsInstDecl  loc [apt[dt,apt[xt,yt]]] (apt [ct,apt [bt,xt]]) []
                ])
        , ("",
                [ hsDataDecl  loc [] [at] [] []
                , hsClassDecl loc [] (apt [ct,xt]) [ hsTypeSig loc [fn] [] (xt `arr` xt) ]
                , hsInstDecl  loc [] (apt [ct,at]) 
                        [ hsTypeSig loc [fn] [] (xt `arr` xt) 
                        , hsFunBind loc [HsMatch loc fn [xp] (HsBody(hsEVar xn)) []] 
                        , hsFunBind loc [HsMatch loc gn [xp] (HsBody(hsEVar yn)) []] 
                        ]
                ])
        , ("OK", [ hsDataDecl  loc [] [at] [] []
                 , hsDataDecl  loc [] [bt,xt] [] []
                 , hsClassDecl loc [] (apt [ct,xt]) []
                 , hsClassDecl loc [] (apt [dt,xt]) []
                 , hsInstDecl  loc [] (apt [ct,at]) []
                 , hsInstDecl  loc [apt [dt,xt]] (apt [ct,apt [bt,xt]]) []
                 ])
        , ("class/type name conflict", 
                 [ hsDataDecl  loc [] [at] [] []
                 , hsDataDecl  loc [] [bt] [] []
                 , hsInstDecl loc [] (apt [at,bt]) []
                 , hsInstDecl loc [] (apt [ct,bt]) []
                 ] )
                           
        ]

dts  = [ ("", [ hsDataDecl  loc [] [at,bt] [] [] ] )
       , ("", [ hsDataDecl  loc [] [xt,yt] [] [] ] )
       ]

clss = [ ("OK", [hsClassDecl loc [] (apt [ct,xt]) []])
       , ("ill formed class specification", [hsClassDecl loc [] (ct) []])
       , ("ill formed class specification", [hsClassDecl loc [] (xt) []])
       , ("class/type name conflict", 
                [ hsDataDecl  loc [] [at] [] []
                , hsDataDecl  loc [] [bt] [] []
                , hsClassDecl loc [] (apt [at,xt]) []
                , hsClassDecl loc [] (apt [bt,xt]) []
                ] )
       , ("ill formed class specification", 
                [  hsClassDecl loc [] (apt [ct,at]) []
                ] )
       , ("ill formed class specification", 
                [  hsClassDecl loc [] (apt [ct,at]) []
                ,  hsClassDecl loc [] (apt [dt,at]) []
                ] )
       , ("ill formed class specification", 
                [ hsDataDecl  loc [] [at] [] []
                , hsClassDecl loc [] (apt [ct,at]) []
                ] )
       , ("",
                [  hsClassDecl loc [] (apt [ct,xt])
                   [ hsTypeSig loc [fn] [] (arr xt xt)
                   , hsPatBind loc fp (HsBody (hsLambda [xp] xe)) []
                   , hsPatBind loc gp (HsBody (hsLambda [xp] xe)) []
                   ]
                ] )
       ]
      
patBind p e = hsPatBind loc p (HsBody e) []

d1 = [patBind fp (hsLambda [xp] xe), patBind fp (hsLambda [xp] (xe))]
{-
p2 = [hsTypeSig loc [zn] (TypeUnQual$ hsTyCon (UnQual "Int"))]
p3 = [hsTypeSig loc [yn,yn] (TypeUnQual $ Typ $ HsTyCon (UnQual "Int"))]
p4 = [patBind fp (hsLet [patBind xp ye] xe)]
p5 = [patBind fp (hsLambda [xp] (ye))]
p6 = [patBind fp (hsLambda [hsPTuple [xp, xp], xp] ye)]
p7 = [patBind fp (hsLambda [hsPTuple [xp, xp, xp], xp] ye)]

runP p = let (envt,f) = chP loc p in f (envt env0)
-}
