[![MELPA](https://melpa.org/packages/counsel-projectile-badge.svg)](https://melpa.org/#/counsel-projectile)

# Description

[Projectile](https://github.com/bbatsov/projectile) has native support for using [ivy](https://github.com/abo-abo/swiper) as its completion system. Counsel-projectile provides further ivy integration into projectile by taking advantage of ivy's mechanism to select from a list of actions and/or apply an action without leaving the completion session. It is inspired by [helm-projectile](https://github.com/bbatsov/helm-projectile).

# Installation

Install the package from [MELPA](https://melpa.org) or [el-get](https://github.com/dimitri/el-get), or clone this repository somewhere in your load path.

# Basic setup

You can use counsel-projectile (and in particular call the command `counsel-projectile` described below with <kbd>C-c p SPC</kbd>) without setting up anything. If you want counsel-projectile to install replacements for some standard projectile commands (see below again), add the following to your init file:

	(counsel-projectile-on)

# Usage

The main command is `counsel-projectile`, and can be called with <kbd>C-c p SPC</kbd> (assuming the variable `projectile-keymap-prefix` has been left at its default value, <kbd>C-c p</kbd>). This command behaves differently depending on whether you call it from inside a project or not:
- If you are not inside a project, it calls the function `counsel-projectile-switch-project`. This uses ivy to display a list of all known projects and let you select a project to switch to. You can choose from a number of actions to be applied upon switching (using <kbd>M-o</kbd> or <kbd>C-M-o</kbd>, as usual with ivy).
- If you are inside a project, it instead uses ivy to display a list of all project buffers and files. The project buffers are fontified, and the project files that are not currently open are shown as "virtual buffers" with a different font (as in the function `ivy-switch-buffer`). You can choose to visit the selected file / display the selected buffer in the current or another window. If you would rather switch to a different project, you can so with <kbd>M-SPC</kbd>.

Counsel-projectile also provides replacements for several standard projectile commands, which take advantage of ivy to let you choose from several actions. To install these replacements, call the command `counsel-projectile-on`. Here are the currently defined replacements, with their default key-bindings:
- <kbd>C-c p f</kbd> `counsel-projectile-find-file`: find a project file,
- <kbd>C-c p d</kbd> `counsel-projectile-find-dir`: find a project directory,
- <kbd>C-c p b</kbd> `counsel-projectile-switch-to-buffer`: switch to a project buffer,
- <kbd>C-c p s s</kbd> `counsel-projectile-ag`: search project files with ag,
- <kbd>C-c p p</kbd> `counsel-projectile-switch-project`: switch to another project (see above).

If your default action for switching to a project (stored in the variable `projectile-switch-project-action`) is `projectile-find-file` (the default), then `counsel-projectile-on` also replaces it with `counsel-projectile`.

You can call the command `counsel-projectile-off` to undo all changes made by `counsel-projectile-on`.

# Contributors

Many thanks to [abo-abo](https://github.com/abo-abo) and [DamienCassou](https://github.com/DamienCassou) who encouraged and helped me to start this repository.
