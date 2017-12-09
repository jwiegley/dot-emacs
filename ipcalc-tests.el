
;; eval this buffer to run the tests

(load-file "ipcalc.el")
(require 'ipcalc)

(ert-deftest int-to-bin-string-test ()
  "Test the conversion of a integer to a binary"
  (should (equal "00000000" (ipcalc-int-to-bin-string 0)))
  (should (equal "00000001" (ipcalc-int-to-bin-string 1)))
  (should (equal "11111111" (ipcalc-int-to-bin-string 255))))

(ert-deftest network-test ()
  "Test the network function"
  (should (string-equal (ipcalc-network "192.168.0.23" "21")
                        "11000000101010000000000000000000")))

(ert-deftest octets-as-binary-test ()
  (should (string-equal (ipcalc-octets-as-binary '("192" "168" "0" "23"))
                        "11000000101010000000000000010111")))

(ert-deftest ip-to-octets-test ()
  "That a IP address gets split into octets"
  (should (equal (ipcalc-ip-to-octets "192.168.0.23")
                 '("192" "168" "0" "23"))))

(ert-deftest ones-and-pad-test ()
  "That padding occurs for a given value"
  (should (string-equal "10000000000000000000000000000000" (ipcalc-ones-and-pad 1)))
  (should (string-equal "11111111111111111111111111111110" (ipcalc-ones-and-pad 31))))

(ert-deftest invert-binary-test ()
  "Tests that it inverts 1s & 0s"
  (should (string-equal (ipcalc-invert-binary "1") "0"))
  (should (string-equal (ipcalc-invert-binary "0") "1")))


(ert-deftest host+1-test ()
  "Add 1 to an binary number"
  (should (equal (ipcalc-host+1 "11000000101010000000000000000000")
                 "11000000101010000000000000000001")))

(ert-deftest host-max-test ()
  "Return the maximum host as a binary value"
  (should (equal (ipcalc-host-max "11000000101010000000000000000000" "21")
                 "11000000101010000000011111111110")))

(ert-deftest binary-to-ip-test ()
  "Convert a IP in binary format to four octets separated by dots"
  (should (equal (ipcalc-binary-to-ip "11000000101010000000000000010111")
                 "192.168.0.23")))

(ert t)
