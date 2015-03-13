module TiFields where
-- Type checking fields


data R = A {a::Int} | B {b::Bool}

-- These are all type correct, but additional checks are needed to make
-- sure that labels are used in a sensible way...

upd r = r{a=1,b=False}

r = A{b=True,a=2}

upd' r@A{a=x} = r{b=x/=0}

f A{a=a,b=b} = (a,b)
g r = (a r,b r)
