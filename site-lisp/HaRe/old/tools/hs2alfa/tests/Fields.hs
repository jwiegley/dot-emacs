module Fields where

data Point = P {x,y::Int} | Q {z::Int}

origin = P { x=0, y=0 }
h = P {x=1,y=1}
v = origin {y=1}

u = P {}

sq x = x*x

dist1 p = sq (x p) + sq (y p)

dist2 P{x=x,y=y} = sq x+sq y

--data Z = Z {z::Int}

data Thread s = T { name::String, status::s}
data Running = Running
data Runanble = Runnable (IO())


makeRunning t = t{status=Running}
