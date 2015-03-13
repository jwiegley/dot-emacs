module RecordIn1 where


data T = Person {name :: String, age :: Int} |
         Animal {name :: String}


getName :: T -> String
getName x = ""