# ovpn-mode
An openvpn management mode for Emacs24+ that lets you start|stop|restart openvpn configurations.

![ovpn-mode screenshot](ovpn-mode.png?raw=true "ovpn-mode")

You can see a demo of the UI in action at https://www.youtube.com/watch?v=48rqO9sR6Io

## general usage
`M-x ovpn` will pop you into the default configuration directory and list any existing .ovpn files from there. You can then interact with that listing with the following single key commands:

- `s`: start the selected ovpn
- `n`: start the selected ovpn in a dedicated namespace
- `q`: stop the selected ovpn
- `r`: restart the selected ovpn

There's a simple color coding scheme that tells you which state a given ovpn is in:

- red: ovpn has stopped/dropped/broken, use `q` to reset/purge, or `b` to debug
- pink: VPN is in the process of initializing
- blue: namespaced VPN is ready for use
- green: system wide VPN is ready for use

Additionally you have available:

- `i`: remote link info for the selected ovpn
- `b`: switch to the output buffer for the selected ovpn
- `e`: edit the selected ovpn
- `d`: set the active vpn conf directory
- `6`: toggle ipv6 support on/off (automatically called on start of ovpn)
- `x`: execute an asynchronous shell command in the context of any associated namespace
- `X`: spawn an xterm in the context of any associated namespace
- `C`: spawn a google-chrome instance with a dedicated data directory in the context of any associated namespace
- `a`: show all active vpn configurations accross all conf directories
- `h`: describe mode

`M-x ovpn-mode-dir-set` lets you point ovpn-mode at any additional directories. ovpn-mode will maintain state for any running configurations, so you can switch between multiple directories and keep state accordingly. This is what `d` is bound to. If you're juggling lots of directories, `a` lets you switch to a view that shows all active ovpn configurations.

## namespace integration

This is currently in beta. By starting a configuration with `n` as opposed to `s` you will set up a dedicated network namespace for the openvpn instance to run inside of. Once this namespace is initialized, you can then use `x` to execute commands as a specified user from within that namespace. You can do this for multiple concurrent vpn connections, without affecting your existing main networking routes. I've had as many as 20 concurrent namespaced ovpn configurations running, without any issues.

This is convenient to e.g. isolate a specific process to a certain vpn without having to do a bunch of routing. Personally I just spawn an xterm from a namespace and then do whatever I want for that specific vpn instance from that xterm (e.g. start rtorrent, an incognito browser session, etc.)

Convenience commands are `X` to spawn an xterm inside the namespace as a specified user, and `C` to spawn an incognito Google Chrome session with some minor lock-down configurations enabled (e.g. --user-data-dir set to a temporary /dev/shm directory, plugins disabled, client side phishing callbacks disabled, etc.).

As mentioned previously `x` allows you to manually run commands inside of a selected namespaced ovpn, but please read `C-h f ovpn-mode-async-shell-command RET` before you do, for some notes on secure use. It's easy to shoot yourself in the foot here by flawed shell escapes that will lead to execution outside the context of the network namespace.  

Namespace instances will automagically drop the default route for the namespace as soon as the vpn connection is fully initialized. This prevents any process being able to connect out via your default system route (i.e. your real IP address) if a VPN configuration were to fail.

To set the default DNS servers to use in these namespaces you can alter `ovpn-mode-netns-ns0` and `ovpn-mode-netns-ns0` through the customize interface under the `ovpn` group (M-x customize RET).

These are treated as default nameservers for any active namespaces, however _IF_ you receive a dhcp-option DNS push from the server in a namespaced context, ovpn-mode will override these default settings with those provided by the server. You need this behavior to work smoothly with e.g. vpn providers that provide .onion name resolution for a tor bridge. 

This work was inspired by crasm's vpnshift.sh script (https://github.com/crasm/vpnshift.sh) but implemented in elisp and enhanced to allow for concurrent namespaces and multiple ovpns running at the same time, with minimal user configuration overhead.

## privilege handling

All sudo privilege handling happens through the emacs TRAMP layer. The initial versions of ovpn-mode include custom sudo handling, but this opened potential attack surface through ovpn server log tampering to match our sudo password prompt regex. Not in any directly exploitable way, but enough to make me completely remove any manual sudo privilege handling from the ovpn-mode code. So all privilege handling just occurs through "/sudo::/tmp" TRAMP paths and start-file-process now

## authinfo support

Default OpenVPN user/pass prompts are supported for transparent authinfo integration for people that want to maintain OpenVPN credentials from their authinfo.gpg file. It expects an authinfo entry that looks like: `machine CONFIGN.OVPN login USER password PASS`

There are two customizable variables that control this behavior. `ovpn-mode-authinfo-path` which is a string that is the path to your authinfo data (defaults to "~/.authinfo.gpg") and `ovpn-mode-check-authinfo` which is a boolean that toggles authinfo checking on/off (defaults to `t`).

## notes
This is something I wrote to fit my exact use case (i.e. I like to be able to pop into and out of multiple openvpn configurations). It should work on any UNIX-like system that has sudo and openvpn available but I've only tested it on Linux.

