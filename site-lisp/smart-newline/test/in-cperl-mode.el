(require 'test-helper)

(defun cperl-mode-setting ()
  (defalias 'perl-mode 'cperl-mode)
  (require 'cperl-mode)
  (cperl-mode)
  (setq cperl-close-paren-offset -4)
  (setq cperl-continued-statement-offset 4)
  (setq cperl-indent-level 4)
  (setq cperl-indent-parens-as-block t)
  (setq cperl-tab-always-indent t)
  (setq cperl-auto-newline nil))

(defun insert-newline-once-in-cperl-mode ()
  (cperl-mode-setting)
  (smart-newline))

(defun insert-newline-twice-in-cperl-mode ()
  (cperl-mode-setting)
  (smart-newline)
  (smart-newline))

(defun insert-newline-triple-in-cperl-mode ()
  (cperl-mode-setting)
  (smart-newline)
  (smart-newline)
  (smart-newline))

(ert-deftest test-cperl-mode-01 ()
  "insert newline at end of line in cperl-mode."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
sub foo {
|}
"
            :exercise 'insert-newline-once-in-cperl-mode)
   :expect (cursor-test/setup
            :init "
sub foo {
    |
}
")))

(ert-deftest test-cperl-mode-02 ()
  "insert newline at end of line in cperl-mode."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
    sub foo {
    |}
"
            :exercise 'insert-newline-once-in-cperl-mode)
   :expect (cursor-test/setup
            :init "
    sub foo {
        |
    }
")))

(ert-deftest test-cperl-mode-03 ()
  "insert newline at end of line in cperl-mode."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
    sub foo {
        |
    }
"
            :exercise 'insert-newline-once-in-cperl-mode)
   :expect (cursor-test/setup
            :init "
    sub foo {

        |
    }
")))

(ert-deftest test-cperl-mode-04 ()
  "insert newline at end of line in cperl-mode."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
    sub foo {

        |
    }
"
            :exercise 'insert-newline-once-in-cperl-mode)
   :expect (cursor-test/setup
            :init "
    sub foo {

        |

    }
")))

(ert-deftest test-cperl-mode-05 ()
  "insert newline at end of line in cperl-mode."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
    sub foo {
        my $self = shift;
        |return $self->foo;
    }
"
            :exercise 'insert-newline-once-in-cperl-mode)
   :expect (cursor-test/setup
            :init "
    sub foo {
        my $self = shift;
        |
        return $self->foo;
    }
")))

(ert-deftest test-cperl-mode-06 ()
  "insert newline at end of line in cperl-mode."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
{
    my $hash = {|};
};
"
            :exercise 'insert-newline-twice-in-cperl-mode)
   :expect (cursor-test/setup
            :init "
{
    my $hash = {
        |
    };
};
")))
