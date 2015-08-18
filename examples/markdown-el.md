# linked-buffer.el --- One buffer as a view of another 

## Code

This is an example markdown file with some embedded code. At the moment,
lentic does not support markdown so this is an expression of interest rather
than an example. Pull requests are welcome.

    (defvar linked-buffer-init 'linked-buffer-default-init
      "Function that initializes a linked-buffer. This should set up
    `linked-buffer-config' appropriately and do")
    
In future versions, this may get turned into a list so that we can have
multiple linked buffers, but it is not clear how the user interface
functions such as `linked-buffer-swap-window` would work now.

    (defvar linked-buffer-config nil
      "Configuration for linked-buffer.

    This is a `linked-buffer-configuration' object, which defines the
    way in which the text in the different buffers is kept
    synchronized. This configuration is resiliant to changes of mode
    in the current buffer.")
    
    (make-variable-buffer-local 'linked-buffer-config)
    (put 'linked-buffer-config 'permanent-local t)

And here is some more documentation.

    (defun linked-buffer-config-name (buffer)
      (format "linked: %s" buffer))

