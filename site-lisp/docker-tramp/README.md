# docker-tramp - TRAMP integration for docker containers

*Author:* Mario Rodas <marsam@users.noreply.github.com><br>
*Version:* 0.1<br>

`docker-tramp.el` offers a TRAMP method for Docker containers.

> **NOTE**: `docker-tramp.el` relies in the `docker exec` command.  Tested
> with docker version 1.6.x but should work with versions >1.3

## Usage

Offers the TRAMP method `docker` to access running containers

    C-x C-f /docker:user@container:/path/to/file

    where
      user           is the user that you want to use (optional)
      container      is the id or name of the container

## Troubleshooting

### Tramp hangs on Alpine container

Busyboxes built with the `ENABLE_FEATURE_EDITING_ASK_TERMINAL` config option
send also escape sequences, which `tramp-wait-for-output` doesn't ignores
correctly.  Tramp upstream fixed in [98a5112][] and is available since
Tramp>=2.3.

For older versions of Tramp you can dump [docker-tramp-compat.el][] in your
`load-path` somewhere and add the following to your `init.el`, which
overwrites `tramp-wait-for-output` with the patch applied:

        (require 'docker-tramp-compat)

[98a5112]: http://git.savannah.gnu.org/cgit/tramp.git/commit/?id=98a511248a9405848ed44de48a565b0b725af82c
[docker-tramp-compat.el]: https://github.com/emacs-pe/docker-tramp.el/raw/master/docker-tramp-compat.el


---
Converted from `docker-tramp.el` by [*el2markdown*](https://github.com/Lindydancer/el2markdown).
