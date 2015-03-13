all: extra_files

extra_files: I_say_so_icons QuickCheckIcons AlfaFiles TestCaseIcons

L=../lib/Programatica
C=$L/types/certificate
S=../../../../../evman/servers

SERVERS=I_say_so QuickCheck Alfa Plover TestCase Cut Isabelle
# Mono

lib::
	@$(MAKE) extra_files
	@sh install.sh $(SERVERS)
	@cd $L; ln -s ../../evman/functions.sh .
	@cd $L; ln -s ../../evman/validation.sh .


################################################################################

I=servers/I_say_so
I_say_so_icons: $I/valid.gif $I/invalid.gif $I/unknown.gif

$I/valid.gif: ;	@ln -sf ../../icons/blue.gif $I/valid.gif
$I/invalid.gif: ; @ln -sf ../../icons/blue_X.gif $I/invalid.gif
$I/unknown.gif: ; @ln -sf ../../icons/blue_Question.gif $I/unknown.gif

################################################################################

Q=servers/QuickCheck
QuickCheckIcons: $Q/valid.gif $Q/invalid.gif $Q/unknown.gif

$Q/unknown.gif: ; @ln -sf icons/quick_check_Unknown.gif $Q/unknown.gif
$Q/invalid.gif: ; @ln -sf icons/quick_check_Fail.gif $Q/invalid.gif
$Q/valid.gif: ; @ln -sf icons/quick_check_OK.gif $Q/valid.gif

################################################################################

A=servers/Alfa
AS=../../../hs2alfa/tests

AlfaFiles: $A/Haskell.alfa $A/Logic.alfa $A/Integer.alfa

$A/Haskell.alfa: ; @cd $A; ln -s $(AS)/Haskell.alfa .
$A/Logic.alfa: ; @cd $A; ln -s $(AS)/Logic.alfa .
$A/Integer.alfa: ; @cd $A; ln -s $(AS)/Integer.alfa .


################################################################################
T=servers/TestCase
TestCaseIcons: $T/valid.gif $T/invalid.gif $T/unknown.gif

$T/unknown.gif: ; @ln -sf ../../icons/testcase_unknown.gif $T/unknown.gif
$T/invalid.gif: ; @ln -sf ../../icons/testcase_invalid.gif $T/invalid.gif
$T/valid.gif: ; @ln -sf ../../icons/testcase_valid.gif $T/valid.gif


################################################################################

clean:
