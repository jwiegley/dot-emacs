module Demote.MultiLeg where

data Constraint = Include String
                | Exclude String
               deriving (Show)

is_excluded stringQueueName (Include regex) = do
  reg <- mkr regex
  return True
is_excluded stringQueueName (Exclude regex) = do
  reg <- mkr regex
  return False

mkr reg = show reg
