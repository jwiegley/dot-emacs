module RecordIn1 where


data T = Person {name :: String, age :: Int} |
         Animal {name :: String}


getName :: T -> String
getName x@(Person b_1 b_2) = ""
getName x@(Animal b_1) = ""
getName x = ""