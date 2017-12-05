(require 'ert)

(defvar refine--test-var)

(ert-deftest refine-movement-nil ()
  "Ensure that movement commands work for the empty list."
  (setq refine--test-var nil)
  (refine 'refine--test-var)
  (refine-next 1)
  (refine-previous 1))

(ert-deftest refine-movement-nil-repeated-forward ()
  "Ensure that repeated forward movement commands work for the
empty list."
  (setq refine--test-var nil)
  (refine 'refine--test-var)
  (let (pos)
    (refine-next 1)
    (setq pos (point))
    ;; Moving forward again should not change our position
    (refine-next 1)
    (should (equal (point) pos))))

