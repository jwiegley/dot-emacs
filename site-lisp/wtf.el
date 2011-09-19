;;; wtf.el --- Look up conversational and computing acronyms

;; Copyright (C) 2005, 2006, 2007 Michael Olson

;; Author: Michael Olson <address@hidden>
;; Date: Wed 16-May-2007
;; Version: 2.0
;; URL: http://mwolson.org/static/dist/elisp/wtf.el

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; wtf.el provides the ability to look up the definitions of popular
;; conversational and computing acronyms.

;; * Use:
;;
;; To use this, move to an unknown acronym in a buffer and type
;; the following:
;;
;;   M-x wtf-is RET
;;
;; The `wtf-is' function may also be called noninteractively, and it
;; will return a string (or nil) rather than displaying a message.
;;
;; To add a custom acronym definition, either customize
;; `wtf-custom-alist' or do:
;;
;;   M-x wtf-add RET <acronym> RET <definition> RET
;;
;; To remove a custom acronym definition, or mark a pre-defined
;; acronym as "removed" in the case that no custom acronym definition
;; exists in `wtf-custom-alist' for that acronym, do:
;;
;;   M-x wtf-remove RET <acronym> RET
;;
;; To mark a pre-defined acronym as "removed", without checking first
;; to see whether it is in `wtf-custom-alist', customize the
;; `wtf-removed-acronyms' option.
;;
;; If you add a custom acronym definition, and feel it to be worth
;; sharing, you are encouraged to contact <address@hidden> via email,
;; providing the acronym and its definition.  This increases the
;; chance that it will appear in future versions of wtf.el.

;; * Legalese:
;;
;; Many of the acronym definitions were downloaded from
;; http://cvsweb.netbsd.org/bsdweb.cgi/src/share/misc/.  No copyright
;; notice was included, but the intent of the original author was to
;; put these acronym definitions in the public domain.  This was
;; deduced from several emails sent to the authors of these files.
;; Additionally, the original data files use a specific syntax which
;; does not allow for a copyright notice.
;;
;; The original program that uses these files in NetBSD
;; (http://cvsweb.netbsd.org/bsdweb.cgi/src/games/wtf/wtf) is in the
;; public domain.

;; * Acknowledgments:
;;
;; Thanks to Trent Buck for `emacs-wiki-wtf.el', which inspired the
;; creation of `wtf.el'.

;;; History:

;; 2.0:
;;
;; - Add the `wtf-custom-alist' option, the `wtf-add' interactive
;;   function to add acronyms to it, and the `wtf-remove' interactive
;;   function to remove acronyms from it.  Thanks to Andreas Roehler
;;   for the suggestion.
;;
;; - Add a few acronyms that were scavenged from various forum FAQ
;;   pages.
;;
;; - Handle multiple definitions for a single acronym more
;;   intuitively.  The text separator used in this case may be changed
;;   by customizing the `wtf-def-separator' option.

;; 1.1-1.4:
;;
;; - Fix a bug with completions in Emacs 21, thanks to Ehud Karni.
;;
;; - Add additional acronyms and re-sync with the NetBSD acronym list.

;; 1.0: Initial release.

;;; Code:

(eval-when-compile (require 'cus-edit))

(defgroup wtf nil
  "Options controlling the behavior of the wtf program.
wtf provides the `wtf-is' command, which looks up the definition
of the acronym at point."
  :group 'convenience)

(defcustom wtf-custom-alist nil
  "Custom mappings of acronyms to definitions used by `wtf-is'.
The acronym should be uppercase, and the definition may be either
lowercase or mixed case.  If mixed case, it will not be modified,
otherwise initial letters will be capitalized.

These definitions are consulted after those in `wtf-alist'.

This variable can also be manipulated interactively by using
`wtf-add'."
  :type '(repeat (cons (string :tag "Acronym")
                       (string :tag "Definition")))
  :group 'wtf)

(defcustom wtf-removed-acronyms nil
  "Acronyms which exist in `wtf-alist' but should be ignored by `wtf-is'.
Each acronym should be in uppercase.
This is an easy way of removing an acronym that is felt to be
wrong or irrelevant.

This variable can also be manipulated interactively by using
`wtf-remove'."
  :type '(repeat (string :tag "Acronym"))
  :group 'wtf)

(defcustom wtf-def-separator ", or "
  "Separator used when an acronym has two or more definitions."
  :type 'string
  :group 'wtf)

(defvar wtf-alist
  '(;; $NetBSD: acronyms,v 1.164 2007/01/31 18:37:07 elad Exp $
    ("AFAIC" . "as far as i'm concerned")
    ("AFAICR" . "as far as i can recall")
    ("AFAICT" . "as far as i can tell")
    ("AFAIK" . "as far as i know")
    ("AFAIR" . "as far as i recall")
    ("AFAIU" . "as far as i understand")
    ("AFD" . "away from desktop")
    ("AFK" . "away from keyboard")
    ("AFU" . "all fucked up")
    ("AFW" . "away from window")
    ("AIU" . "as i understand")
    ("AIUI" . "as i understand it")
    ("AKA" . "also known as")
    ("ASAIC" . "as soon as i can")
    ("ASAP" . "as soon as possible")
    ("ATM" . "at the moment")
    ("AWOL" . "absent without official leave")
    ("AYBABTU" . "all your base are belong to us")
    ("AYT" . "are you there")
    ("B/C" . "because")
    ("B/S" . "bullshit")
    ("B/W" . "between")
    ("BBIAB" . "be back in a bit")
    ("BBL" . "[I'll] Be Back Later")
    ("BBS" . "be back soon")
    ("BBT" . "be back tomorrow")
    ("BFD" . "big fucking deal")
    ("BIAB" . "back in a bit")
    ("BIAF" . "back in a few")
    ("BIALW" . "back in a little while")
    ("BIAS" . "back in a second")
    ("BIAW" . "back in a while")
    ("BOATILAS" . "bend over and take it like a slut")
    ("BOFH" . "bastard operator from hell")
    ("BOGAHICA" . "bend over, grab ankles, here it comes again")
    ("BOHICA" . "bend over here it comes again")
    ("BRB" . "[I'll] Be Right Back")
    ("BS" . "bullshit")
    ("BTDT" . "been there, done that")
    ("BTTH" . "boot to the head")
    ("BTW" . "by the way")
    ("CMIIW" . "correct me if i'm wrong")
    ("CNP" . "continued [in my] next post")
    ("COB" . "close of business [day]")
    ("COTS" . "commercial off-the-shelf")
    ("CYA" . "see you around")
    ("D/L" . "download")
    ("DGAS" . "don't give a shit")
    ("DIY" . "do it yourself")
    ("DKDC" . "don't know, don't care")
    ("DSTM" . "don't shoot the messenger")
    ("DTRT" . "do the right thing")
    ("DTWT" . "do the wrong thing")
    ("DWIM" . "do what i mean")
    ("EG" . "evil grin")
    ("EMSG" . "email message")
    ("EOB" . "end of business [day]")
    ("EOD" . "end of discussion")
    ("EOL" . "end of life")
    ("ETA" . "estimated time of arrival")
    ("ETLA" . "extended three letter acronym")
    ("EWAG" . "experienced wild-ass guess")
    ("FAQ" . "frequently asked question")
    ("FCFS" . "first come first served")
    ("FIGJAM" . "fuck i'm good, just ask me")
    ("FIIK" . "fuck[ed] if i know")
    ("FIIR" . "fuck[ed] if i remember")
    ("FM" . "fucking magic")
    ("FOAD" . "fall over and die")
    ("FOS" . "full of shit")
    ("FSDO" . "for some definition of")
    ("FSVO" . "for some value of")
    ("FTFM" . "fuck the fuckin' manual!")
    ("FTL" . "for the loss")
    ("FTW" . "for the win")
    ("FUBAR" . "fucked up beyond all recognition")
    ("FUD" . "fear, uncertainty and doubt")
    ("FWIW" . "for what it's worth")
    ("FYI" . "for your information")
    ("G" . "grin")
    ("G/C" . "garbage collect")
    ("GAC" . "get a clue")
    ("GAL" . "get a life")
    ("GIGO" . "garbage in, garbage out")
    ("GMTA" . "great minds think alike")
    ("GTFO" . "get the fuck out")
    ("GTG" . "got to go")
    ("GWS" . "get well soon")
    ("HAND" . "have a nice day")
    ("HHIS" . "hanging head in shame")
    ("HICA" . "here it comes again")
    ("HTH" . "hope this helps")
    ("IAC" . "in any case")
    ("IANAL" . "i am not a lawyer")
    ("IC" . "i see")
    ("ICBW" . "i could be wrong")
    ("ICCL" . "i couldn't care less")
    ("IHAFC" . "i haven't a fucking clue")
    ("IHBW" . "i have been wrong")
    ("IHNFC" . "i have no fucking clue")
    ("IIANM" . "if i am not mistaken")
    ("IIRC" . "if i recall correctly")
    ("IIUC" . "if i understand correctly")
    ("IMAO" . "in my arrogant opinion")
    ("IMCO" . "in my considered opinion")
    ("IMHO" . "in my humble opinion")
    ("IMNSHO" . "in my not so humble opinion")
    ("IMO" . "in my opinion")
    ("IOW" . "in other words")
    ("IRL" . "in real life")
    ("ISAGN" . "i see a great need")
    ("ISTM" . "it seems to me")
    ("ISTR" . "i seem to recall")
    ("ITYM" . "i think you mean")
    ("IWBNI" . "it would be nice if")
    ("IYSS" . "if you say so")
    ("J/K" . "just kidding")
    ("JHD" . "just hit ``delete''")
    ("JIC" . "just in case")
    ("JK" . "just kidding")
    ("JMO" . "just my opinion")
    ("JSYK" . "just so you know")
    ("JTLYK" . "just to let you know")
    ("KISS" . "keep it simple, stupid")
    ("KITA" . "kick in the ass")
    ("KNF" . "kernel normal form")
    ("L8R" . "later")
    ("LART" . "luser attitude readjustment tool (ie, hammer)")
    ("LBNL" . "last but not least")
    ("LGTM" . "looks good to me")
    ("LJBF" . "let's just be friends")
    ("LMAO" . "laughing my ass off")
    ("LMSO" . "laughing my socks off")
    ("LOL" . "laughing out loud")
    ("LTNS" . "long time no see")
    ("MIA" . "missing in action")
    ("MOTAS" . "member of the appropriate sex")
    ("MOTOS" . "member of the opposite sex")
    ("MOTSS" . "member of the same sex")
    ("MTF" . "more to follow")
    ("MYOB" . "mind your own business")
    ("N/M" . "never mind")
    ("NBD" . "no big deal")
    ("NFC" . "no fucking clue")
    ("NFI" . "no fucking idea")
    ("NFW" . "no fucking way")
    ("NIH" . "not invented here")
    ("NMF" . "not my fault")
    ("NMP" . "not my problem")
    ("NOYB" . "none of your business")
    ("NOYFB" . "none of your fucking business")
    ("NP" . "no problem")
    ("NRFPT" . "not ready for prime time")
    ("NRN" . "no reply necessary")
    ("NSFW" . "not suitable for work")
    ("OIC" . "oh, i see")
    ("OMG" . "oh, my god")
    ("OT" . "off topic")
    ("OTL" . "out to lunch")
    ("OTOH" . "on the other hand")
    ("OTT" . "over the top")
    ("OTTOMH" . "off the top of my head")
    ("PDQ" . "pretty darn quick")
    ("PEBKAC" . "problem exists between keyboard and chair")
    ("PFO" . "please fuck off")
    ("PFY" . "pimply faced youth")
    ("PITA" . "pain in the ass")
    ("PKSP" . "pound keys and spew profanity")
    ("PNG" . "persona non grata")
    ("PNP" . "plug and pray")
    ("POC" . "point of contact")
    ("POLA" . "principle of least astonishment")
    ("POLS" . "principle of least surprise")
    ("POS" . "piece of shit")
    ("PPL" . "pretty please")
    ("PTV" . "parental tunnel vision")
    ("QED" . "quod erat demonstrandum")
    ("RFC" . "request for comments")
    ("RIP" . "rest in peace")
    ("RL" . "real life")
    ("RLC" . "rod length check")
    ("ROFL" . "rolling on floor laughing")
    ("ROFLMAO" . "rolling on floor laughing my ass off")
    ("ROTFL" . "rolling on the floor laughing")
    ("RP" . "responsible person")
    ("RSN" . "real soon now")
    ("RTFB" . "read the fine/fucking book")
    ("RTFC" . "read the fine/fucking code")
    ("RTFD" . "read the fine/fucking documentation")
    ("RTFM" . "read the fine/fucking manual")
    ("RTFMP" . "read the fine/fucking man page")
    ("RTFS" . "read the fine/fucking source")
    ("SCNR" . "sorry, could not resist")
    ("SEP" . "someone else's problem")
    ("SFA" . "sweet fuck all")
    ("SHID" . "slaps head in disgust")
    ("SIMCA" . "sitting in my chair amused")
    ("SMLSFB" . "so many losers, so few bullets")
    ("SMOP" . "simple matter of programming")
    ("SNAFU" . "situation normal, all fucked up")
    ("SNERT" . "snot-nosed egotistical rude teenager")
    ("SNMP" . "sorry, not my problem")
    ("SNR" . "signal to noise ratio")
    ("SO" . "significant other")
    ("SOB" . "son of [a] bitch")
    ("SOL" . "shit out [of] luck")
    ("SOP" . "standard operating procedure")
    ("SSIA" . "subject says it all")
    ("SSTO" . "single stage to orbit")
    ("STFA" . "search the fucking archives")
    ("STFU" . "shut the fuck up")
    ("STFW" . "search the fucking web")
    ("SUS" . "stupid user syndrome")
    ("SWAG" . "silly, wild-assed guess")
    ("SWAHBI" . "silly, wild-assed hare-brained idea")
    ("SWFG" . "search with fucking google")
    ("SWMBO" . "she who must be obeyed")
    ("TANSTAAFL" . "there ain't no such thing as a free lunch")
    ("TBC" . "to be continued")
    ("TBD" . "to be {decided,determined,done}")
    ("TBH" . "to be honest")
    ("TBOMK" . "the best of my knowledge")
    ("THNX" . "thanks")
    ("THX" . "thanks")
    ("TIA" . "thanks in advance")
    ("TINC" . "there is no cabal")
    ("TLA" . "three letter acronym")
    ("TLC" . "tender loving care")
    ("TLDR" . "too long, didn't read")
    ("TMA" . "too many abbreviations")
    ("TMI" . "too much information")
    ("TMTOWTDI" . "there's more than one way to do it")
    ("TNF" . "The NetBSD Foundation")
    ("TOEFL" . "test of english as a foreign language")
    ("TPTB" . "the powers that be")
    ("TRT" . "the right thing")
    ("TTBOMK" . "to the best of my knowledge")
    ("TTFN" . "ta ta for now")
    ("TTYL" . "talk to you later")
    ("TWIAVBP" . "the world is a very big place")
    ("TY" . "thank you")
    ("TYVM" . "thank you very much")
    ("U/L" . "upload")
    ("UTSL" . "use the source, luke")
    ("VEG" . "very evil grin")
    ("W/" . "with")
    ("W/O" . "without")
    ("WAG" . "wild-ass guess")
    ("WB" . "welcome back")
    ("WFH" . "working from home")
    ("WFM" . "works for me")
    ("WIBNI" . "wouldn't it be nice if")
    ("WIP" . "work in progress")
    ("WOFTAM" . "waste of fucking time and money")
    ("WOMBAT" . "waste of money, brain, and time")
    ("WRT" . "with respect to")
    ("WTF" . "{what,where,who,why} the fuck")
    ("WTH" . "{what,where,who,why} the hell")
    ("WYSIWYG" . "what you see is what you get")
    ("YALIMO" . "you are lame, in my opinion")
    ("YHBT" . "you have been trolled")
    ("YHL" . "you have lost")
    ("YKWIM" . "you know what i mean")
    ("YMA" . "yo momma's ass")
    ("YMMV" . "your mileage may vary")
    ("YW" . "you're welcome")
    ;; $NetBSD: acronyms.comp,v 1.72 2007/01/19
    ("3WHS" . "three-way handshake")
    ("ABI" . "application binary interface")
    ("ACL" . "access control list")
    ("ACPI" . "advanced configuration and power interface")
    ("ADC" . "analog [to] digital converter")
    ("ADPCM" . "adaptive differential pulse code modulation")
    ("ADSL" . "asymmetric digital subscriber line")
    ("AGP" . "accelerated graphics port")
    ("AM" . "amplitude modulation")
    ("AMI" . "alternate mark inversion")
    ("ANSI" . "american national standards institute")
    ("AP" . "access point")
    ("API" . "application programming interface")
    ("APIC" . "advanced programmable interrupt controller")
    ("ARP" . "address resolution protocol")
    ("ARQ" . "automatic repeat request")
    ("AS" . "autonomous system")
    ("ASCII" . "american standard code for information interchange")
    ("ASN" . "autonomous system number")
    ("AT" . "advanced technology")
    ("ATA" . "advanced technology attachment")
    ("ATAPI" . "advanced technology attachment packet interface")
    ("ATC" . "address translation cache")
    ("ATM" . "asynchronous transfer mode")
    ("ATX" . "advanced technology extended")
    ("BEDO" . "burst extended data output")
    ("BER" . "basic encoding rules")
    ("BER" . "bit error rate")
    ("BGP" . "border gateway protocol")
    ("BIOS" . "basic input/output system")
    ("BLOB" . "binary large object")
    ("BPS" . "bits per second")
    ("BQS" . "berkeley quality software")
    ("BSD" . "berkeley software distribution")
    ("CAD" . "computer-aided design")
    ("CARP" . "common address redundancy protocol")
    ("CAV" . "Constant Angular Velocity (as opposed to CLV)")
    ("CCD" . "charge coupled device")
    ("CD" . "compact disc")
    ("CDDA" . "compact disc digital audio")
    ("CDRAM" . "cache dynamic random access memory")
    ("CER" . "canonical encoding rules")
    ("CGA" . "color graphics {array,adapter}")
    ("CGI" . "common gateway interface")
    ("CHS" . "cylinder/head/sector")
    ("CIDR" . "classless inter-domain routing")
    ("CIS" . "contact image sensor")
    ("CLI" . "command line interface")
    ("CLUT" . "color look-up table")
    ("CLV" . "Constant Linear Velocity (as opposed to CAV)")
    ("CMYK" . "cyan magenta yellow black")
    ("COFF" . "common object file format")
    ("COW" . "copy-on-write")
    ("CPU" . "central processing unit")
    ("CRLF" . "carriage return line feed")
    ("CRT" . "cathode ray tube")
    ("CSMA" . "carrier sense multiple access")
    ("CSMA/CA" . "carrier sense multiple access with collision avoidance")
    ("CSMA/CD" . "carrier sense multiple access with collision detection")
    ("CSS" . "cascading style sheets")
    ("CTS" . "clear to send")
    ("CVS" . "concurrent versions system")
    ("DAC" . "digital [to] analog converter")
    ("DCE" . "data control equipment")
    ("DCE" . "distributed computing environment")
    ("DCT" . "discrete cosine transform")
    ("DDC" . "display data channel")
    ("DDR" . "double data rate")
    ("DDWG" . "digital display working group")
    ("DER" . "distinguished encoding rules")
    ("DFT" . "discrete fourier transform")
    ("DHCP" . "dynamic host configuration protocol")
    ("DIFS" . "distributed inter-frame space")
    ("DLE" . "data link escape")
    ("DMA" . "direct memory access")
    ("DNS" . "domain name system")
    ("DOS" . "denial of service")
    ("DPCM" . "differential pulse code modulation")
    ("DPD" . "dead peer detection")
    ("DPI" . "dots per inch")
    ("DRAM" . "dynamic random access memory")
    ("DSL" . "digital subscriber line")
    ("DSSS" . "direct sequence spread spectrum")
    ("DTD" . "document type definition")
    ("DTE" . "data terminal equipment")
    ("DTE" . "dumb terminal emulator")
    ("DVD" . "digital versatile disc")
    ("DVI" . "digital visual interface")
    ("E-XER" . "Extended XML encoding Rules")
    ("EAP" . "extensible authentication protocol")
    ("ECP" . "enhanced capability port")
    ("EDID" . "extended display identification data")
    ("EDO" . "extended data out")
    ("EEPROM" . "electrically erasable programmable read only memory")
    ("EFI" . "extensible firmware interface")
    ("EFM" . "eight to fourteen modulation")
    ("EGA" . "enhanced graphics {array,adapter}")
    ("EGP" . "exterior gateway protocol")
    ("EISA" . "extended industry standard architecture")
    ("ELF" . "executable and linking format")
    ("EOF" . "end of file")
    ("EOT" . "end of transmission")
    ("EPP" . "enhanced parallel port")
    ("EPRML" . "extended partial response, maximum likelihood")
    ("EPROM" . "erasable programmable read only memory")
    ("ESDRAM" . "enhanced synchronous dynamic random access memory")
    ("FAT" . "file allocation table")
    ("FBRAM" . "frame buffer random access memory")
    ("FCS" . "frame check sequence")
    ("FDDI" . "fiber distributed data interface")
    ("FFS" . "fast file system")
    ("FHSS" . "frequency hop spread spectrum")
    ("FIR" . "fast infrared")
    ("FLOPS" . "floating [point] operations per second")
    ("FM" . "frequency modulation")
    ("FPM" . "fast page mode")
    ("FQDN" . "fully qualified domain name")
    ("FTP" . "file transfer protocol")
    ("FTPS" . "file transfer protocol, secure")
    ("GC" . "garbage collector")
    ("GCR" . "group-coded recording")
    ("GIF" . "graphics interchange format")
    ("GNU" . "GNU's Not UNIX")
    ("GPL" . "GNU/General Public License")
    ("GPU" . "graphics processing unit")
    ("GRE" . "generic routing encapsulation")
    ("GUI" . "graphics user interface")
    ("HDCP" . "high-bandwidth digital content protection")
    ("HTML" . "hyper-text markup language")
    ("HTTP" . "hyper-text transfer protocol")
    ("HTTPS" . "hyper-text transfer protocol, secure")
    ("I2O" . "intelligent input/output")
    ("IANA" . "internet assigned number authority")
    ("IC" . "integrated circuit")
    ("ICB" . "internet citizen's band")
    ("ICMP" . "internet control message protocol")
    ("IDE" . "integrated drive electronics")
    ("IDRP" . "inter-domain routing protocol")
    ("IEC" . "international electrotechnical commission")
    ("IEEE" . "institute [of] electrical [and] electronics engineers")
    ("IESG" . "internet engineering steering group")
    ("IETF" . "internet engineering task force")
    ("IGP" . "interior gateway protocol")
    ("IKE" . "internet key exchange")
    ("IMAP" . "internet mail access protocol")
    ("INCITS" . "international committee on information technology standards")
    ("IO" . "input/output")
    ("IOCTL" . "input/output control")
    ("IP" . "internet protocol")
    ("IPC" . "interprocess communication")
    ("IPNG" . "internet protocol, next generation")
    ("IPSEC" . "internet protocol security")
    ("IRC" . "internet relay chat")
    ("IRQ" . "interrupt request")
    ("IRTF" . "internet research task force")
    ("ISA" . "industry standard architecture")
    ("ISDN" . "integrated services digital network")
    ("ISI" . "inter-symbol interference")
    ("ISM" . "industrial, scientific and medical")
    ("ISN" . "initial serial number")
    ("ISO" . "international standards organization")
    ("ISOC" . "internet society")
    ("ISP" . "internet service provider")
    ("JPEG" . "joint photographic experts group")
    ("KPI" . "kernel programming interface")
    ("KVA" . "kernel virtual address")
    ("KVM" . "keyboard, video, mouse switch")
    ("LAN" . "local area network")
    ("LBA" . "logical block addressing")
    ("LCD" . "liquid crystal display")
    ("LCP" . "link control protocol")
    ("LDAP" . "lightweight directory access protocol")
    ("LED" . "light emitting diode")
    ("LIR" . "local internet registry")
    ("LKM" . "{linux, loadable} kernel module")
    ("LLC" . "logical link control")
    ("LRC" . "longitudinal redundancy check")
    ("LSB" . "least significant {bit,byte}")
    ("LSB" . "linux standards base")
    ("LUN" . "logical unit number")
    ("LZW" . "Lempel Ziv Welch")
    ("MAC" . "medium access control")
    ("MBR" . "master boot record")
    ("MDRAM" . "multibank dynamic random access memory")
    ("MFM" . "modified frequency modulation")
    ("MIDI" . "musical instrument digital interface")
    ("MIME" . "multipurpose internet mail extensions")
    ("MIPS" . "million instructions per second")
    ("MMU" . "memory management unit")
    ("MPEG" . "moving picture experts group")
    ("MPLS" . "multiprotocol label switching")
    ("MSB" . "most significant {bit,byte}")
    ("MSF" . "minutes seconds frames")
    ("MSS" . "maximum segment size")
    ("MTA" . "mail transfer agent")
    ("MTU" . "maximum transmission unit")
    ("MUA" . "mail user agent")
    ("MWE" . "module width encoding")
    ("NAT" . "network address translation")
    ("NAV" . "network allocation vector")
    ("NCP" . "network control protocol")
    ("NCQ" . "native command queuing")
    ("NFS" . "network file system")
    ("NIC" . "network interface card")
    ("NIS" . "network information service")
    ("NRZ" . "non-return to zero")
    ("NUMA" . "non uniform memory access")
    ("OCL" . "object constraint language")
    ("OCR" . "optical character recognition")
    ("OEM" . "original equipment manufacturer")
    ("OFDM" . "orthogonal frequency division multiplexing")
    ("OSF" . "open software foundation")
    ("OSI" . "open systems interconnection")
    ("OSI" . "open-source initiative")
    ("OSPF" . "open shortest path first")
    ("OTP" . "one time password")
    ("PAM" . "pluggable authentication modules")
    ("PAM" . "pulse amplitude modulation")
    ("PAT" . "port address translation")
    ("PAX" . "portable archive exchange")
    ("PC" . "personal computer")
    ("PCI" . "peripheral component interconnect")
    ("PCM" . "pulse code modulation")
    ("PCMCIA" . "personal computer memory card international association")
    ("PDP" . "page descriptor page")
    ("PDU" . "protocol data unit")
    ("PER" . "packed encoding rules")
    ("PERL" . "practical extraction [and] report language")
    ("PFS" . "perfect forward secrecy")
    ("PGP" . "pretty good privacy")
    ("PIC" . "programmable interrupt controller")
    ("PID" . "process id")
    ("PIN" . "personal identification number")
    ("PIO" . "programmed input/output")
    ("PLL" . "phase locked loop")
    ("PMT" . "photo-multiplier tube")
    ("PNG" . "portable network graphics")
    ("POP" . "post office protocol")
    ("POSIX" . "Portable Operating System Interface [for] UNIX")
    ("POST" . "power on self test")
    ("POTS" . "plain old telephone system")
    ("PPP" . "point-to-point protocol")
    ("PPPOA" . "point-to-point protocol over ATM")
    ("PPPOE" . "point-to-point protocol over ethernet")
    ("PRML" . "partial response, maximum likelihood")
    ("PROM" . "programmable read only memory")
    ("PSK" . "pre-shared key")
    ("PSTN" . "public switched telephone network")
    ("PTE" . "page table entry")
    ("PTLA" . "pseudo top level aggregator")
    ("PTP" . "page table page")
    ("PWM" . "pulse width modulation")
    ("QOS" . "quality of service")
    ("RAID" . "redundant array of inexpensive disks")
    ("RAM" . "random access memory")
    ("RCS" . "revision control system")
    ("RGB" . "red green blue")
    ("RIFF" . "Resource Interchange File Format")
    ("RIP" . "routing information protocol")
    ("RIR" . "regional internet registry")
    ("RISC" . "reduced instruction set computing")
    ("RLE" . "run length encoding")
    ("RLL" . "run length limited")
    ("ROM" . "read only memory")
    ("RPM" . "revolutions per minute")
    ("RTF" . "rich text format")
    ("RTS" . "request to send")
    ("RTT" . "round time trip")
    ("S/PDIF" . "sony/phillips digital interface")
    ("SACD" . "super audio compact disc")
    ("SAD" . "security association database")
    ("SAM" . "serial access memory")
    ("SASI" . "Shugart Associates System Interface (predecessor to SCSI)")
    ("SATA" . "serial advanced technology attachment")
    ("SB" . "sound blaster")
    ("SCM" . "software configuration management")
    ("SCM" . "source code management")
    ("SCSI" . "small computer system interface")
    ("SDRAM" . "synchronous dynamic random access memory")
    ("SGRAM" . "synchronous graphics random access memory")
    ("SIFS" . "short inter-frame space")
    ("SIP" . "session initiation protocol")
    ("SIR" . "slow infrared")
    ("SLDRAM" . "synchronous-link dynamic random access memory")
    ("SMART" . "self-monitoring analysis and reporting technology")
    ("SMP" . "symmetric multiprocessing")
    ("SMTP" . "simple mail transfer protocol")
    ("SNMP" . "simple network management protocol")
    ("SPD" . "security policy database")
    ("SPD" . "serial presence detect")
    ("SRAM" . "static random access memory")
    ("SSFDC" . "solid state floppy disc card")
    ("SSH" . "secure shell")
    ("SSL" . "secure sockets layer")
    ("STP" . "shielded twisted pair")
    ("SVGA" . "super video graphics {array,adapter}")
    ("TCL" . "tool command language")
    ("TCP" . "transmission control protocol")
    ("TCQ" . "tagged command queueing")
    ("TDD" . "test driven development")
    ("TFT" . "thin film transistor")
    ("TFTP" . "trivial file transfer protocol")
    ("TIFF" . "tagged image file format")
    ("TLA" . "top level aggregator")
    ("TLB" . "transition lookaside buffer")
    ("TLD" . "top level domain")
    ("TLS" . "transport layer security")
    ("TMDS" . "transition minimized differential signaling")
    ("TR" . "token ring")
    ("TTL" . "time to live")
    ("TTY" . "teletype")
    ("TZ" . "time zone")
    ("UART" . "universal asynchronous receiver/transmitter")
    ("UC" . "uncacheable")
    ("UDO" . "ultra density optical (storage)")
    ("UDP" . "user datagram protocol")
    ("UFS" . "UNIX file system")
    ("UML" . "unified modeling language")
    ("UPS" . "uninterruptible power supply")
    ("URI" . "uniform resource identifier")
    ("URL" . "uniform resource locator")
    ("USART" . "universal synchronous/asynchronous receiver/transmitter")
    ("USB" . "universal serial bus")
    ("USWC" . "uncacheable speculative write combining")
    ("UTP" . "unshielded twisted pair")
    ("UUCP" . "unix-to-unix copy protocol")
    ("UUOC" . "useless use of cat")
    ("VAX" . "virtual address extension")
    ("VCM" . "virtual channel memory")
    ("VESA" . "video electronics standards association")
    ("VGA" . "video graphics {array,adapter}")
    ("WIFI" . "wireless fidelity")
    ("VLAN" . "virtual local area network")
    ("VLSM" . "variable length subnet mask")
    ("VM" . "virtual {machine,memory}")
    ("VPN" . "virtual private network")
    ("VRAM" . "video random access memory")
    ("VRRP" . "virtual router redundancy protocol")
    ("WAN" . "wide area network")
    ("WAP" . "wireless application protocol")
    ("WEP" . "wired equivalent privacy")
    ("WLAN" . "wireless local area network")
    ("WPA" . "wi-fi protected access")
    ("WRAM" . "window random access memory")
    ("WWW" . "world wide web")
    ("XER" . "XML Encoding Rules")
    ("XGA" . "extended graphics {array,adapter}")
    ("XML" . "extensible markup language")
    ("XSL" . "extensible stylesheet language")
    ("XT" . "extended technology")
    ("ZFOD" . "zero-filled on demand")
    ;; Additional acronym definitions go here
    ("AAMOF" . "as a matter of fact")
    ("AISI" . "as i see it")
    ("ASAIMS" . "as strange as it may seem")
    ("ATSL" . "along the same line")
    ("AYOR" . "at your own risk")
    ("BTAIM" . "be that as it may")
    ("BTDTBTTS" . "been there, done that, bought the t-shirt")
    ("BTHOM" . "beats the hell outta me")
    ("CBA" . "can't be arsed")
    ("DBD" . "Defective By Design")
    ("DIIK" . "damned if i know")
    ("EFF" . "Electronic Frontier Foundation")
    ("FFII" . "Foundation for a Free Information Infrastructure")
    ("FOAF" . "friend of a friend")
    ("FSF" . "Free Software Foundation")
    ("FTR" . "for the record")
    ("FTBFS" . "failure to build from source")
    ("GAFC" . "get a fucking clue")
    ("IAE" . "in any event")
    ("IBTD" . "i beg to differ")
    ("ICBF" . "i can't be fucked")
    ("IDS" . "intrusion detection system")
    ("IDK" . "i don't know")
    ("IJWTS" . "i just want to say")
    ("IME" . "in my experience")
    ("IYSWIM" . "if you see what i mean")
    ("JFTR" . "just for the record")
    ("NIFOC" . "naked in front of computer")
    ("NPOV" . "neutral point of view")
    ("PITB" . "pain in the butt")
    ("POV" . "point of view")
    ("ROTFLMAO" . "rolling on the floor laughing my ass off")
    ("SWIM" . "see what i mean")
    ("TNSTAAFL" . "there's no such thing as a free lunch")
    ("TWAT" . "the war against terrorism")
    ("WDOT" . "what do others think")
    ("WDYMBT" . "what do you mean by that")
    ("WDYT" . "what do you think")
    ("WTB" . "where's the beef")
    ("WTSHTF" . "when the shit hits the fan")
    ("WTTM" . "without thinking too much")
    ("WOTAM" . "waste of time and money")
    ("YAGNI" . "you ain't gonna need it")
    ("YGWYPF" . "you get what you pay for"))
  "Mapping of acronyms to definitions.")

;;; Utilities

(defun wtf-match-string-no-properties (num &optional string)
  "Return NUMth match of STRING sans text properties."
  (if (fboundp 'match-string-no-properties)
      (match-string-no-properties num string)
    (match-string num string)))

(defun wtf-remove-one (key alist)
  "Remove only the first instance of KEY from ALIST.
ALIST should be a symbol, the value of which is modified directly.
Returns non-nil if an element was found and removed, nil otherwise."
  (let ((svalist (symbol-value alist)))
    (if (equal key (caar svalist))
        (prog1 t
          (set alist (cdr svalist)))
      (catch 'done
        (let ((cur (cadr svalist))
              (prev svalist))
          (while cur
            (if (equal key (car cur))
                (throw 'done
                       (prog1 t
                         (setcdr prev (cddr prev))))
              (setq prev (cdr prev)
                    cur (cadr prev))))
          nil)))))

(defun wtf-multi-assoc (key &rest alists)
  "Return a list of all values in all ALISTS that are associated with KEY."
  (let ((vals nil))
    (dolist (alist alists)
      (dolist (pair alist)
        (when (equal key (car pair))
          (setq vals (cons (cdr pair) vals)))))
    (nreverse vals)))

(defun wtf-upcase-initials (string)
  "Do `upcase-initials' on STRING, but do not uppercase letters
that come after quote characters.

This function clobbers the match data."
  (with-temp-buffer
    (insert (upcase-initials string))
    (goto-char (point-min))
    (while (re-search-forward "['`]\\([[:upper:]]\\)" nil t)
      (downcase-region (match-beginning 1) (match-end 1)))
    (buffer-string)))

(defun wtf-upcase-initials-maybe (string)
  "Do `wtf-upcase-initials' on STRING only if STRING contains no
existing capitalization.

This function clobbers the match data."
  (let ((case-fold-search nil))
    (if (string-match "[A-Z]" string)
        string
      (wtf-upcase-initials string))))

;;; Implementation

(defun wtf-lookup-term (term)
  (setq term (upcase term))
  (wtf-multi-assoc term
                   (and (not (member term wtf-removed-acronyms))
                        wtf-alist)
                   wtf-custom-alist))

(defun wtf-get-term-at-point ()
  "Return the term at point."
  (interactive)
  (save-excursion
    (if (re-search-backward "\\W" (point-min) t)
        (goto-char (1+ (point)))
      (beginning-of-line))
    (when (looking-at "\\w+")
      (let ((term (wtf-match-string-no-properties 0)))
        (when (wtf-lookup-term term)
          (downcase term))))))

(defun wtf-completions ()
  "Return a list of completions for terms."
  (mapcar #'(lambda (term)
              (list (downcase (car term))))
          (append wtf-alist wtf-custom-alist)))

(defun wtf-save-maybe (var)
  "If customizations are allowed, save VAR, which should be a symbol."
  (when (fboundp 'customize-save-variable)
    (customize-save-variable var (symbol-value var))
    (message "Saved wtf customization")))

;;; Interactive functions

;;;###autoload
(defun wtf-add (acronym definition)
  "Add ACRONYM and its DEFINITION to the list of custom associations.

If you add a custom acronym definition, and feel it to be worth
sharing, you are encouraged to contact <address@hidden> via
email, providing the acronym and its definition.  This increases
the chance that it will appear in future versions of wtf.el."
  (interactive "sAcronym: \nsDefinition: ")
  (setq acronym (upcase acronym))
  (setq wtf-custom-alist (sort (cons (cons acronym definition)
                                     wtf-custom-alist)
                               #'(lambda (a b)
                                   (string< (car a) (car b)))))
  (wtf-save-maybe 'wtf-custom-alist))

;;;###autoload
(defun wtf-remove (acronym)
  "Remove ACRONYM from the list of custom associations.
If ACRONYM is not in the custom associations, but instead in
`wtf-alist', it will be marked as ignored by adding it to
`wtf-removed-acronyms'."
  (interactive
   (list (completing-read "Acronym to remove: "
                          (wtf-completions) nil t (wtf-get-term-at-point))))
  (setq acronym (upcase acronym))
  (if (wtf-remove-one acronym 'wtf-custom-alist)
      (wtf-save-maybe 'wtf-custom-alist)
    (add-to-list 'wtf-removed-acronyms acronym)
    (wtf-save-maybe 'wtf-removed-acronyms)))

;;;###autoload
(defun wtf-is (acronym)
  "Provide the definition for ACRONYM.
When called interactively, display the message \"ACRONYM is DEF\".
Otherwise, return DEF.

DEF refers to the definition associated with ACRONYM in `wtf-alist'."
  (interactive
   (list (completing-read "Acronym: "
                          (wtf-completions) nil t (wtf-get-term-at-point))))
  (when (stringp acronym)
    (let ((defs (wtf-lookup-term acronym)))
      (if (not defs)
          (when (interactive-p)
            (message "I don't know what %s means" (upcase acronym)))
        (save-match-data
          (let ((deftext (wtf-upcase-initials-maybe (car defs))))
            (when (cdr defs)
              (dolist (def (cdr defs))
                (setq deftext (concat deftext wtf-def-separator
                                      (wtf-upcase-initials-maybe def)))))
            (if (interactive-p)
                (message "%s is %s" (upcase acronym) deftext)
              deftext)))))))

(provide 'wtf)

;;; wtf.el ends here
