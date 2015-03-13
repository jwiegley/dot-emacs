-- $Id: AccList.hs,v 1.1 2001/09/06 02:12:55 hallgren Exp $

module AccList (accList) where


accList acc [] ans     = ans
accList acc (x:xs) ans = accList acc xs (acc x ans) -- LEFT-TO-RIGHT here

-- Property: accList == flip . foldl . flip
