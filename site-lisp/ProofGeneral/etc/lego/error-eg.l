Init LF;

[prop:Type];
[prf:prop->Type];
[type:Type];
[el:type->Type];

[FA : {A:type}((el A) -> prop) -> prop];
[LL : {A:type}{P:(el A) -> prop}
          ({x:el A}prf(P(x)))->
   (********************************)
      	  prf(FA A P)];

[P_FA : {A:type}{P:(el A) -> prop}{C_FA:prf(FA A P) -> prop}
      	  ((g:{x:el A}prf(P(x)))prf(C_FA(LL A P g))) -> 
			  {z:prf(FA A P)}prf(C_FA(z))];