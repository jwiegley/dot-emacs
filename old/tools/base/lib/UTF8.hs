module UTF8 where

-- From the Char module supplied with HBC.

-- Take a Unicode string and encode it as a string
-- with the UTF8 method.
decodeUTF8 :: String -> String
decodeUTF8 "" = ""
decodeUTF8 (c:cs) | c < '\x80' = c : decodeUTF8 cs
decodeUTF8 (c:c':cs) | '\xc0' <= c  && c  <= '\xdf' && 
		      '\x80' <= c' && c' <= '\xbf' =
	toEnum ((fromEnum c `mod` 0x20) * 0x40 + fromEnum c' `mod` 0x40) : decodeUTF8 cs
decodeUTF8 (c:c':c'':cs) | '\xe0' <= c   && c   <= '\xef' && 
		          '\x80' <= c'  && c'  <= '\xbf' &&
		          '\x80' <= c'' && c'' <= '\xbf' =
	toEnum ((fromEnum c `mod` 0x10 * 0x1000) + (fromEnum c' `mod` 0x40) * 0x40 + fromEnum c'' `mod` 0x40) : decodeUTF8 cs
decodeUTF8 _ = error "UniChar.decodeUTF8: bad data"

encodeUTF8 :: String -> String
encodeUTF8 "" = ""
encodeUTF8 (c:cs) =
	if c > '\x0000' && c < '\x0080' then
	    c : encodeUTF8 cs
	else if c < toEnum 0x0800 then
	    let i = fromEnum c
	    in  toEnum (0xc0 + i `div` 0x40) : 
	        toEnum (0x80 + i `mod` 0x40) : 
		encodeUTF8 cs
	else
	    let i = fromEnum c
	    in  toEnum (0xe0 + i `div` 0x1000) : 
	        toEnum (0x80 + (i `mod` 0x1000) `div` 0x40) : 
		toEnum (0x80 + i `mod` 0x40) : 
		encodeUTF8 cs
