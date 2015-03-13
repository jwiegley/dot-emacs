module Time {-(
        ClockTime, 
        Month(January,February,March,April,May,June,
              July,August,September,October,November,December),
        Day(Sunday,Monday,Tuesday,Wednesday,Thursday,Friday,Saturday),
	CalendarTime(CalendarTime, ctYear, ctMonth, ctDay, ctHour, ctMin,
     ctPicosec, ctWDay, ctYDay, ctTZName, ctTZ, ctIsDST),
	TimeDiff(TimeDiff, tdYear, tdMonth, tdDay, 
	 tdHour, tdMin, tdSec, tdPicosec),
        getClockTime, addToClockTime, diffClockTimes,
        toCalendarTime, toUTCTime, toClockTime,
        calendarTimeToString, formatCalendarTime )-} where

import Prelude
import Ix(Ix)
import Locale --(TimeLocale(..),defaultTimeLocale)
import Char ( intToDigit )

newtype ClockTime
   = ClockTime Int
  deriving (Eq,Ord,Show)
  -- The Show instance is a deviation from Haskell 98, provided for
  -- compatibility with Hugs and GHC.

data Month =  January   | February | March    | April
           |  May       | June     | July     | August
           |  September | October  | November | December
           deriving (Eq, Ord, Enum, Bounded, Ix, Read, Show)
--instance Enum Month

data Day   =  Sunday | Monday  | Tuesday  | Wednesday | Thursday 
           |  Friday | Saturday
           deriving (Eq, Ord, Enum, Bounded, Ix, Read, Show)
--instance Enum Day

data CalendarTime = CalendarTime {
                ctYear                          :: Int,
                ctMonth                         :: Month,
                ctDay, ctHour, ctMin, ctSec     :: Int,
                ctPicosec                       :: Integer,
                ctWDay                          :: Day,
                ctYDay                          :: Int,
                ctTZName                        :: String,
                ctTZ                            :: Int,
                ctIsDST                         :: Bool
        } deriving (Eq, Ord, Read, Show)

data TimeDiff = TimeDiff {
                tdYear, tdMonth, tdDay, tdHour, tdMin, tdSec :: Int,
                tdPicosec                                    :: Integer
        } deriving (Eq, Ord, Read, Show)


getClockTime            :: IO ClockTime
getClockTime            = undefined           -- Implementation-dependent

addToClockTime          :: TimeDiff     -> ClockTime -> ClockTime
addToClockTime td ct    =  undefined          -- Implementation-dependent

diffClockTimes          :: ClockTime    -> ClockTime -> TimeDiff
diffClockTimes ct1 ct2  =  undefined          -- Implementation-dependent

toCalendarTime          :: ClockTime    -> IO CalendarTime
toCalendarTime ct       =  undefined          -- Implementation-dependent

toUTCTime               :: ClockTime    -> CalendarTime
toUTCTime ct            =  undefined          -- Implementation-dependent

toClockTime             :: CalendarTime -> ClockTime
toClockTime cal         =  undefined          -- Implementation-dependent

calendarTimeToString    :: CalendarTime -> String
calendarTimeToString    =  formatCalendarTime defaultTimeLocale "%c"

formatCalendarTime :: TimeLocale -> String -> CalendarTime -> String
formatCalendarTime l fmt ct@(CalendarTime year mon day hour min sec sdec 
                                           wday yday tzname _ _) =
        doFmt fmt
  where doFmt ('%':c:cs) = decode c ++ doFmt cs
        doFmt (c:cs) = c : doFmt cs
        doFmt "" = ""

        to12 :: Int -> Int
        to12 h = let h' = h `mod` 12 in if h' == 0 then 12 else h'

        decode 'A' = fst (wDays l  !! fromEnum wday)
        decode 'a' = snd (wDays l  !! fromEnum wday)
        decode 'B' = fst (months l !! fromEnum mon)
        decode 'b' = snd (months l !! fromEnum mon)
        decode 'h' = snd (months l !! fromEnum mon)
        decode 'C' = show2 (year `quot` 100)
        decode 'c' = doFmt (dateTimeFmt l)
        decode 'D' = doFmt "%m/%d/%y"
        decode 'd' = show2 day
        decode 'e' = show2' day
        decode 'H' = show2 hour
        decode 'I' = show2 (to12 hour)
        decode 'j' = show3 yday
        decode 'k' = show2' hour
        decode 'l' = show2' (to12 hour)
        decode 'M' = show2 min
        decode 'm' = show2 (fromEnum mon+1)
        decode 'n' = "\n"
        decode 'p' = (if hour < 12 then fst else snd) (amPm l)
        decode 'R' = doFmt "%H:%M"
        decode 'r' = doFmt (time12Fmt l)
        decode 'T' = doFmt "%H:%M:%S"
        decode 't' = "\t"
        decode 'S' = show2 sec
        --decode 's' = undefined                -- Implementation-dependent
        decode 'U' = show2 ((yday + 7 - fromEnum wday) `div` 7)
        decode 'u' = show (let n = fromEnum wday in 
                           if n == 0 then 7 else n)
        decode 'V' = 
            let (week, days) = 
                   (yday + 7 - if fromEnum wday > 0 then 
                               fromEnum wday - 1 else 6) `divMod` 7
            in  show2 (if days >= 4 then
                          week+1 
                       else if week == 0 then 53 else week)

        decode 'W' = 
            show2 ((yday + 7 - if fromEnum wday > 0 then 
                               fromEnum wday - 1 else 6) `div` 7)
        decode 'w' = show (fromEnum wday)
        decode 'X' = doFmt (timeFmt l)
        decode 'x' = doFmt (dateFmt l)
        decode 'Y' = show year
        decode 'y' = show2 (year `rem` 100)
        decode 'Z' = tzname
        decode '%' = "%"
        decode c   = [c]

show2, show2', show3 :: Int -> String
show2 x = [intToDigit (x `quot` 10), intToDigit (x `rem` 10)]

show2' x = if x < 10 then [ ' ', intToDigit x] else show2 x

show3 x = intToDigit (x `quot` 100) : show2 (x `rem` 100)
