# 0.8.0

- [X] Update travis ci configuration
- [X] Fix ci's multiple problems
- [X] Fix some emacs25 incompatibilities
- [X] Add copyright headers + update copyright range
- [X] Add 'kill-whole-line in bug report
- [X] Upgrade version
- [X] Release notes

# 0.7.9

- [X] Fix problem with custom kill-whole-line properties - Close #270
- [X] Fix problem with scheduled deadline - Close #326
- [X] Upgrade version
- [X] Release notes

# 0.7.8

- [X] Fix cyrillic encoding problem - Close #318 #270
- [X] Update version
- [X] Sign tag release
- [X] Release notes

# 0.7.7

- [X] Rework packaging problem
- [X] Add issue/pr templates
- [X] Add request-backend to the org-trello-bug-report
- [X] Update version
- [X] Release notes

# 0.7.6

- [X] Update version
- [X] Support unicode characters in sync - Close #307 Close #309
- [X] Fix parsing username comments - Close #301
- [X] Fix parsing timestamp in superior emacs (api change)
- [X] Update travis-ci scripts to use the new travis infrastructure
- [X] fix broken tests (mock.el unit test library revealed broken tests)
- [X] Fix problem with org-latex-preview when computing checksums - Close #303
- [X] Do not permit empty login when installing access key and token - Close #314
- [X] Upgrade dependencies version
- [X] Pb with labels-tags regarding the grey - Close #310
- [X] Improve documentation about the setup account - #306
- [X] Release notes

# 0.7.5

- [X] #290 - Toggling users assignments to card
- [X] Add binding `C-c o t` for the toggling command (code, doc, etc...)
- [X] #293 - Add a basic user driven completing mechanism (default ido, possibility to use helm...)
- [X] #291 - Improve labels policy [4/4]
  - [X] Update api to retrieve more labels
  - [X] Unify board information retrieval
  - [X] Update show board labels with the new colors
  - [X] Fix what went wrong (install existing board + create new one)
- [X] Open a command to clean org-trello data in buffer
- [X] Close board command
- [X] Update version
- [X] Release notes

# 0.7.4

- [X] Improve release script + fix typo
- [X] Update version
- [X] Coverage [10/10]
  - [X] stats-coverage.org for statistics (+ travis-ci/coverage.io)
  - [X] Fix bug on org-trello-log namespace + org-trello-log
  - [X] org-trello-input
  - [X] org-trello-query
  - [X] org-trello-proxy
  - [X] org-trello-buffer
  - [X] org-trello-controller
  - [X] org-trello-data
  - [X] org-trello-hash
  - [X] org-trello
- [X] #283 - Toggle assign me action
- [X] Release notes

# 0.7.3

- [X] Update version
- [X] Close #277 - Improve date time policy conversion
- [X] Improve release + upload to marmalade scripts
- [X] Fix flycheck warnings
- [X] Some refactoring
- [X] Release notes

# 0.7.2

- [X] Update version
- [X] Close #276 - Markdown rendering in comments
- [X] Add test coverage
- [X] [internal] Full respect elisp convention
- [X] Release notes

# 0.7.1

- [X] Update version
- [X] Close #272 - Use native completion mechanism
- [X] Close #273 - Fix labels when installing board
- [X] Close #271 - Make a user option for user to decide the policy about checksum and position
- [X] Use improved native completin mechanism (again)
- [X] Close #274 - Add `M-x org-trello-bug-report` command
- [X] Release notes

# 0.7.0

- [X] Update version
- [X] Close #238 - [internal] Respect elisp coding conventions [2/2]
  - [X] Rename constants + variables
  - [X] Rename entry points according to conventions + alias old definitions for backward compatibility
- [X] Close #239 - Migrate ~/.trello/config.el inside user-emacs-directory
- [X] Close #256 - one user can have multiple trello accounts [4/4]
  - [X] Migrate the actual setup to the multi-account setup (transparent for user)
  - [X] Update `org-trello-install-key-and-token` command to create the account setup
  - [X] Update the loading configuration mechanism multi-account aware
  - [X] Make sure initializing org-trello account is ok
- [X] Close #267 - Emptying card's description does not work
- [X] Remove too much verbosity (when deleting property checksum)
- [X] Close #250 - Changing order of checklist items not saved unless checklist item's text changed
- [X] Release notes

# 0.6.9.6

- [X] Create backlog
- [X] Update version
- [X] Fix #261 - Modifying/Adding labels ok, removing labels completely ko
- [X] Fix #262 - Mix between user ids and user name when assigning card
- [X] Release notes

# 0.6.9.5

- [X] Create backlog
- [X] Update version
- [X] Fix marmalade's release.sh script
- [X] Fix #255 regarding the org tags/trello labels
- [X] Release notes

# 0.6.9.4

- [X] Update version
- [X] Fix https://github.com/org-trello/org-trello/issues/252
- [X] Release notes

# 0.6.9.3

- [X] Create backlog
- [X] Update version
- [X] Problem in first comment point computation - Close #242
- [X] Release notes

# 0.6.9.2

- [X] Update version
- [X] Clean dead code regarding old comments system
- [X] Fix bug regarding comments indentation (breaking org rendering)
- [X] Fix bug regarding empty card and next card indentation (breaking org rendering)
- [X] Fix compile log warning about orgtrello-buffer depending on orgtrello-controller (wrong)
- [X] Update README-dev.md
- [X] Release notes

# 0.6.9.1

- [X] Create backlog
- [X] Update version
- [X] Fix region computation problem regarding comments - https://github.com/org-trello/org-trello/issues/232
- [X] Release notes

# 0.6.9

- [X] Create backlog
- [X] Update version
- [X] Fix #+property keyword to #+PROPERTY - CLOSE https://github.com/org-trello/org-trello/issues/234
- [X] Fix missing line on future org-mode 8.3 - CLOSE https://github.com/org-trello/org-trello/issues/232
- [X] Release notes

# 0.6.8

- [X] Create backlog
- [X] Update version
- [X] Edit comment direct in buffer - CLOSE https://github.com/org-trello/org-trello/issues/221
- [X] Open binding `C-c o U` for `sync a comment` action
- [X] Release notes

# 0.6.7

- [X] Create backlog
- [X] Update version
- [X] Improve/Refactor the comment deletion
- [X] Fix `orgtrello-buffer/pop-up-with-content!`
- [X] Improve comment creation - CLOSE https://github.com/org-trello/org-trello/issues/222 [2/2]
  - [X] Add checksum to the comments
  - [X] Improve comment creation
- [X] Release notes

# 0.6.6

- [X] Create backlog
- [X] Update version
- [X] Delete comments - CLOSE https://github.com/org-trello/org-trello/issues/222
- [X] Clean no longer used show comments commands + install the delete comment command
- [X] Release notes

# 0.6.5

- [X] Create backlog
- [X] Update version
- [X] Maintenance - Revert tests back to ert-deftest to have more explicit error outputs
- [X] Fix unit tests
- [X] Fix CI which does not break when failure or error.
- [X] Format user's comments in a readable format - https://github.com/org-trello/org-trello/issues/218 [2/2]
  - [X] Update the comment's format according to https://github.com/org-trello/org-trello/issues/218#issue-48750430
  - [X] Update the `org-trello/add-card-comment` command to improve creating comment
- [X] Release notes

# 0.6.4

- [X] Minor change to allow abbreviated file path - https://github.com/org-trello/org-trello/pull/213
- [X] Update version
- [X] Move file list functionality to org-trello.el - CLOSE https://github.com/org-trello/org-trello/issues/214
- [X] Add ;;;### autoload for the org-trello's default commands
- [X] Release notes

# 0.6.3

- [X] Update version
- [X] Enable org-trello mode automatically for certain files - https://github.com/org-trello/org-trello/issues/210
- [X] Release notes

# 0.6.2

- [X] Backlog
- [X] Update version
- [X] Improve check connection to trello
- [X] Improve documentation about the org-trello setup
- [X] Release notes

# 0.6.1

- [X] Update version
- [X] `Trello archived` cards are not archived on org-trello buffers - CLOSE https://github.com/org-trello/org-trello/issues/203
- [X] Release notes

# 0.6.0

- [X] Refactor - Unify data structure between trello card and org-trello card
- [X] Refactor - Improve merge computations
- [X] Refactor - Remove some dead code
- [X] Update version
- [-] Improve sync request policy - [[https://github.com/org-trello/org-trello/issues/58]] [87%]
  - [X] 'Sync card to trello' syncs card only if local changes
  - [X] 'Sync card from trello' updates the card from trello and the local checksum signature
  - [X] 'Sync buffer from trello' updates the local card checksum
  - [X] 'Sync buffer to trello' syncs only card with local changes
  - [X] 'Delete entity' updates the checksum
  - [X] Extend the checksum system to the checkbox entities (checklist/item) - sync to trello
  - [X] Extend the checksum system to the checkbox entities (checklist/item) - sync from trello
  - [X] Update checksum computation depending on entities
- [X] `Checklists don't work for me` - It does work - Need to improve checklist and item predicates. - CLOSE https://github.com/org-trello/org-trello/issues/204
  - [X] Fix behavior
  - [X] Fix tests
- [X] Release notes

# 0.5.9

- [X] Backlog
- [X] Update version
- [X] Improve region card computation for sync card from trello.
- [X] Fix error on sync card from trello when nothing to sync.
- [X] Use defcustom instead of defvar for user customisation - CLOSE [[https://github.com/org-trello/org-trello/issues/196][#196]]
- [X] When not in card, explain why you cannot do the current action
- [X] Improve display of error when sync a card without title
- [X] Check package installation and fix what's needed
- [X] Release notes

# 0.5.8

- [X] Backlog
- [X] Update version
- [X] Add emacs24 dependencies - https://github.com/purcell/org-trello/commit/0fef27e83d5b1c68af03213354ddd97448c802d2 + http://www.gnu.org/software/emacs/manual/html_node/elisp/Library-Headers.html#Library-Headers + http://stackoverflow.com/questions/16805645/how-can-i-gracefully-drop-support-for-older-emacsen-in-my-elisp-package
- [X] Downgrade request dependency to 0.3.1 to make org-trello installation possible in melpa-stable (no answer from `request` maintainer) + https://github.com/org-trello/org-trello/issues/195
- [X] Release notes

# 0.5.7

- [X] Backlog
- [X] Update version
- [X] Fix default keyword when not specified (trello list name) - [[https://github.com/org-trello/org-trello/issues/183][#183]]
- [X] Remove reference to proxy in log messages
- [X] Sync buffer from trello - Ignore errors when there is nothing to sort.
- [X] Sync buffer from trello - Fold buffer entries when done.
- [X] Fix bug on (orgtrello-entity/compute-card-region!)
- [X] Release notes

# 0.5.6

- [X] backlog
- [X] Update version
- [X] Use save-excursion - save-restriction - narrow-to-region instead of using region
- [X] Fix behavior orgtrello-buffer/end-of-line! When going to end of line in checkbox, we need to do it twice, fix.
- [X] Small refactoring about overlays
- [X] Release notes

# 0.5.5

- [X] Backlog
- [X] Update version
- [X] Update main github's readme to static link to the main documentation site.
- [X] Update bindings order to regroup them
- [X] Add bindings for archiving cards `C-c o A`
- [X] Remove old bindings `C-c o C` that synced the card.
- [X] Update bindings `C-c o A` to add comments to the card to `C-c o A`
- [X] Update bindings to show comments as `C-u C-c o A` and remove the old one `C-c o o`
- [X] Check everything is ok from test point of view
- [X] Fix Synchronization problem - #183
- [X] Some refactoring to reduce multiple buffer readings
- [X] Check package installation
- [X] Release notes

# 0.5.4

- [X] Backlog
- [X] Archive cards - CLOSE #181
  - [X] Open trello api about (un)archive card
  - [X] Refactor API to factorize behavior
  - [X] Install org-trello archive binding [100%]
    - [X] Archive card interactive command
    - [X] Ensure sync-from trello does not retrieve archive cards too
    - [X] Remap org's default archive binding `C-c $` to use org-trello's
    - [X] Functional checks before executing archive
    - [X] Add Archive DONE cards interactive command
- [X] Fix `Most actions not working` issue - CLOSE #192
- [X] Update version
- [X] Fix compilation warning(s)
- [X] Release notes

# 0.5.3

- [X] Backlog
- [X] Emacs blocks when sync - CLOSE #164 - Deferred the sync/delete actions [100%]
  - [X] Align execution of code regarding [100%]
    - [X] Sync to
    - [X] Sync from
    - [X] Delete
  - [X] Render the execution asynchronous [100%]
    - [X] Delete
    - [X] Sync card to trello
    - [X] Sync buffer to trello
    - [X] Sync card from trello
    - [X] Sync buffer from trello
  - [X] Fix alignment problem (sync a card from trello must enforce order on position)
  - [X] Remove dead code
  - [X] Refactor behavior between sync card and sync buffer [100%]
    - [X] Refactor behavior
    - [X] Refactor names
  - [X] Trigger save after sync action - cannot do this because all requests are asynchronous. So emacs will do it on his own.
  - [X] Caret must remain where it stands after `sync from card` action
  - [X] Fix - Keep the order when synchronizing the buffer
  - [X] Improve orgtrello-controller/do-install-key-and-token
  - [X] Improve org-trello/install-board-and-lists-ids [100%]
    - [X] Let trello do the filtering on listing the boards
    - [X] Resequence the actions and use parallel requests to improve speed
    - [X] Improve some more regarding the sequencing
  - [X] Improve org-trello/update-board-metadata [100%]
    - [X] Rework the sequencing
    - [X] Remove intermediary sync request
  - [X] Clean new dead code
  - [X] Improve orgtrello-controller/do-create-board-and-lists [100%]
    - [X] Rename org-trello/create-board to org-trello/create-board-and-install-metadata
    - [X] Resequence the trello requests
    - [X] Clean up some dead code
- [X] Fix caret movement problem (At the end of an action, the caret must be at the same position as before)
- [X] Improve logging system to prefix org-trello message with 'org-trello - '
- [X] Fix create board issue (regarding org keyword list + order + closing list)
- [X] Rename org-trello/install-board-and-lists to org-trello/install-board-metadata
- [X] Rename org-trello/jump-to-card to org-trello/jump-to-trello-card
- [X] Update package doc installation in org-trello.el
- [X] Check package dependencies and adapt them if need be
- [X] Fix problem with org-trello/end-of-line! when there is no org information at point
- [X] Update version
- [X] Release notes

# 0.5.2

- [X] Remove org-trello's over engineered bricks (proxy, elnode, webadmin) -> this will render it synchronous again. [100%]
  - [X] Is proxy useful since emacs still blocks? -> The only thing interesting seems to be the ability to watch running actions. As no one seem to care about it, we can remove it.
  - [X] Can't we simply use 'deferred (or 'async library) to defer computations? -> Yes, building actions (sync, delete) as 'lazy' list (macro) of deferred computations.
  - [X] What about concurrency then? There will be indeed possibilities of concurrent requests.
  - [X] What about race conditions then? We need to find a way to compose deferred computations -> [[https://github.com/kiwanami/emacs-deferred][deferred]] seems able to do so
  - [X] Remove db dependency
  - [X] Remove elnode dependency
  - [X] Remove esxml dependency
  - [X] Remove orgtrello-db.el
  - [X] Remove orgtrello-webadmin.el
  - [X] Remove orgtrello-elnode.el
  - [X] Remove orgtrello-server.el
  - [X] Clean orgtrello-proxy.el up
  - [X] Get back to synchronous query (sync to + delete)
  - [X] Get back to synchronous query for sync from trello routines
  - [X] Clean load-org-trello.el up
  - [X] Update README-dev.md about namespace removal
  - [X] Fix loading of load-org-trello.el code
  - [X] Clean tests up
  - [X] Update org-trello package
- [X] Fix bug regarding sync-entity and structure (apparently, there is a bad limit computation and this syncs the all buffer)
- [X] Fix save buffer at the end of the sync actions
- [X] Clean README-dev.md about marmalade
- [X] Update dependencies version
- [X] Now that elnode, esxml, db dependencies' are out of the way, org-trello can be fully built on melpa-stable.
- [X] Update version
- [X] Clean dead code
- [X] Release notes

# 0.5.1

- [X] Remove marmalade remains (release.sh + Makefile)
- [X] Small refactoring of the main contract
- [X] Fix bad code (typo caddr)
- [X] Update version
- [X] Release notes

# 0.5.0

- [X] Revert 0.4.9 #187 which introduced regressions #186#issuecomment-52423783 and maybe #185
- [X] Retrieve interesting code from 0.4.9 (for example, start proxy during actions if stopped and warn about it, etc...)
- [X] Update version
- [X] Release notes

# 0.4.9

- [X] Backlog
- [X] Emacs blocks when sync - #164
  - [X] deferred dependency - 0.3.1 chosen because it's the common denominator between marmalade and melpa
  - [X] Render the data request consumer asynchoneous
  - ... emacs still blocks though...
- [X] Sometimes the proxy seems to not be started (which is a mess), add a check on the running proxy before doing anything. - #180
- [X] During the check of the proxy, if not started, try to start it.
- [X] Update version
- [X] No longer deliver to marmalade (too much work)
- [X] Release notes

# 0.4.8

- [X] Backlog
- [X] mad caret syndrom - Close #177
  - [X] mad caret - fix sync to
  - [X] mad caret - the caret does not move even when sync computation takes place
  - [X] mad caret - fix sync from
- [X] Upgrade version
- [X] Update release notes

# 0.4.7

- [X] Backlog
- [X] Improve the description management in org and trello - #89 #175
- [X] Revert to the block json-encode-hash-table
- [X] Upgrade version
- [X] Update release notes

# 0.4.6

- [X] Prepare Backlog
- [X] Fix - CLOSE https://github.com/org-trello/org-trello/issues/172
- [X] Fix - prelude does some monkey-patching on json-encode-hash-table which is used by org-trello - reimplement this function
- [X] CI is broken again - Try to find a solution
- [X] Update version
- [X] Update release notes

# 0.4.5

- [X] Backlog
- [X] 'Sync from trello' must preserve unknown data card in drawer - CLOSE #167
  - [X] Extract unknown information and store them in org entity representation
  - [X] Ensure those data transit back in trello data when merging
  - [X] Write back those unknown information in the sync from trello
- [X] Update version
- [X] Release notes

# 0.4.4

- [X] Multiple files packaging - CLOSE #163
  - [X] Move src/*.el files to /org-trello
  - [X] Add 'provide statements for each of those files
  - [X] Rework header + org-trello + footer files
  - [X] Adapt main org-trello.el files to reference the needed namespaces
  - [X] Adapt test files so that it continues to work (add the needed require statements)
  - [X] Adapt loading code routine for developing + testing
  - [X] Refactoring step - rename some files to avoid confusion
  - [X] Adapt README-dev.md to the current code adaptation
  - [X] Adapt cask packaging
  - [X] Add missing standard header to namespace
  - [X] Does org-trello still compiles? NO
  - [X] Fix simple compilation warnings
  - [X] Fix some more warnings
  - [X] Does org-trello's test work? YES
  - [X] Does org-trello work? NO
  - [X] Doc - Update docstring to standard emacs convention
  - [X] Fix org-trello to make it work again
  - [X] Test package melpa install (adapt org-trello recipe and test M-x package-install-file) - https://github.com/ardumont/melpa/blob/org-trello-with-multiple-files-packaging/recipes/org-trello
  - [X] Test package marmalade install
- [X] Fix org-trello behavior with overlay on org-return and org-ctrl-c-ret
- [X] Update version
- [X] Release notes

# 0.4.3

- [X] Prepare backlog
- [X] Replace local back-end (file implementation) with a RAM database [100%]
- [X] Update README-dev.md about the new db namespace
- [X] Remove some useless new code
- [X] Improve start/stop server policy (one server may sync multiple buffers/boards... and right now, not really taken into account)
- [X] Clean dead code from the implementation switch from implicit disk files db to RAM db [100%]
- [X] Improve start/stop server policy 2
- [X] Some Refactoring
- [X] Version
- [X] Release notes

# 0.4.2

- [X] Refactoring - Remove dead code
- [X] Refactoring - Remove duplicated code already existing in dependency library
- [X] Improve - Fold all entries when sync full file from trello is done
- [X] Improve loading org-trello namespaces for dev purposes
- [X] Version
- [X] Release notes

# 0.4.1.1

- [X] Remove non interactive commands
- [X] Create board does not work - Close #157
- [X] Improve loading keys policy - #156
- [X] Use cask to make the packaging and remove old personal routines
- [X] Version
- [X] Release notes

# 0.4.1

- [X] Fix deadline/description problem - #154
- [X] Fix deadline/due date problem - #153
- [X] When sync from trello, merge non trello org tags with trello tags (to avoid loss for the user)
- [X] When sync to trello, filter out org tags that will not be understood by trello (to avoid 400 request from trello)
- [X] Add the quick start in the main package description
- [X] Version
- [X] Release notes

# 0.4.0.1

- [X] Fix 'Sync doesn't work if org buffer name contains special characters' - Close #147
- [X] Version
- [X] Release notes

# 0.4.0

- [X] Refactor
- [X] Fix - Close https://github.com/org-trello/org-trello/issues/145
- [X] Remove unused dependency
- [X] Update README-dev.md
- [X] Version
- [X] Release notes

# 0.3.9

- [X] Refactor - Symmetry for all commands where that makes sense (without C-u/with C-u)
- [X] Refactor - Enforce the api request creation usage with the params as usual
- [X] Let trello filter out needless data - CLOSE https://github.com/org-trello/org-trello/issues/69
  - [X] Let trello filter out needless data - get card
  - [X] Let trello filter out needless data - get checklist
  - [X] Let trello filter out needless data - get item
- [X] Upgrade Version
- [X] Release notes

# 0.3.8

- [X] Some refactoring
  - [X] Align sync from trello card tags/labels serialization with org's tags behavior
  - [X] Refactor open org-trello buffer with title/content
  - [X] Sanitize functions (move functions to their right namespaces)
  - [X] Do not override the user's existing tags
- [X] Provide org-trello-mode-hook - CLOSE https://github.com/org-trello/org-trello/issues/116
- [X] Open stop all synchronization actions - CLOSE https://github.com/org-trello/org-trello/issues/131
- [X] Use C-u keychord to create a symmetry use (e.g. `C-c o s` is sync to trello, `C-u C-c o s` is sync from trello)
  - [X] sync-buffer, sync-to-trello, with C-u, sync-from-trello
  - [X] assign-me, with C-u, unassign me
  - [X] A command to 'sync from trello' the current entity without its structure - CLOSE https://github.com/org-trello/org-trello/issues/139
  - [X] Use C-u on sync-entity-to-trello command to trigger the sync-entity-from-trello
  - [X] A command to 'sync from trello' the current entity and its structure - CLOSE https://github.com/org-trello/org-trello/issues/140
  - [X] Use C-u on sync-entity-and-structure-to-trello command to trigger the sync-entity-and-structure-from-trello
- [X] Some more refactoring
- [X] Fix bug regarding org keywords which disappeared
- [X] Version
- [X] Release notes

# 0.3.7

- [X] Use `defconst` keyword instead of defvar
- [X] Use trello labels and org tags as one - CLOSE https://github.com/org-trello/org-trello/issues/70
- [X] Refactor + Fix create / connect to board
- [X] Update metadata command about the board currently connected (sometimes, new information arise)
- [X] Release notes
- [X] Version

# 0.3.6.1

- [X] Fix already used bindings
- [X] Fix edge case about adding comments
- [X] Version
- [X] Release notes

# 0.3.6

- [X] Test multiple emacs version - https://github.com/org-trello/org-trello/issues/52
- [X] Add a logo to website - https://github.com/org-trello/org-trello/issues/129
- [X] Synchronize user comments - https://github.com/org-trello/org-trello/issues/86
- [X] Add a comment to a card - https://github.com/org-trello/org-trello/issues/132
- [X] Take control over the test file which is now too big (dispatch in 'namespace' test buffer)
- [X] Version
- [X] Release notes

# 0.3.5

- [X] Test multiple emacs version - https://github.com/org-trello/org-trello/issues/52
- [X] Version
- [X] Update documentation note for the package view
- [X] Release note

# 0.3.4

- [X] PR fix typo in readme - https://github.com/org-trello/org-trello/pull/120
- [X] Fix webadmin button to delete running action
- [X] Add version emacs 24.3.50 in documentation
- [X] Improve computation level for checkbox (checklist/items) - https://github.com/org-trello/org-trello/issues/121#issuecomment-37559929
- [X] Improve documentation
- [X] Upgrade version
- [X] Release notes

# 0.3.3

- [X] Issue when installing on melpa reported wrongly on melpa and reported back https://github.com/org-trello/org-trello/issues/117
- [X] Fix typo when-let in -when-let
- [X] Remove org as a dependency, the plugins org- do not seem to declare it + problem in dependency
- [X] Upgrade to dash 2.5.0
- [X] Clarify the possible manipulation to install the package as a file or directly from the multiple repository
- [X] Integration test to install the file with marmalade
- [X] Integration test to install the file with melpa
- [X] Integration test to fully install the package on marmalade
- [X] Integration test to fully install the package on melpa
- [X] Update README-dev.md about those targets
- [X] Decline these tests with multiple emacs versions
- [X] Use these targets on travis (even if the feedback will be way longer, it's better than no feedback)
- [X] Upgrade version
- [X] Ensure org-trello works with emacs 24.4 (how do i install it...)

# 0.3.2

- [X] Use standard remapping to override the org-end-of-line routine - https://www.gnu.org/software/emacs/manual/html_node/elisp/Remapping-Commands.html
- [X] Clean some dead code
- [X] Use standard mode map definition for the org-trello bindings
- [X] Fix description extract - https://github.com/org-trello/org-trello/issues/114
- [X] Version
- [X] Release notes

# 0.3.1.1

- [X] Installation failure - https://github.com/org-trello/org-trello/issues/112
- [X] Version
- [X] Release notes

# 0.3.1

- [X] Backlog
- [X] Version
- [X] Avoid duplication in declaring the org-trello version
- [X] Add the important information about emacs 24.3+ (org-trello is only supported from this version range)
- [X] Clean the code regarding the old checklist/item entities (with stars) - https://github.com/org-trello/org-trello/issues/105
- [X] Sometimes, multiple cards are created more than once. Improve the proxy policy regarding this - Unable to reproduce so do nothing.
- [X] Release notes

# 0.3.0

- [X] Backlog
- [X] Upgrade Version
- [X] org-trello bindings remains present when org-trello is switched off. Fix it.
- [X] Update doc
- [X] Release notes

# 0.2.9.1

- [X] Forgot to ship code
- [X] Update version
- [X] Release notes

# 0.2.9

- [X] Remove org-trello.el at the root of the code (as the package generates this file and the test load without it, no longer needs to be gitted)
- [X] Invisible checkbox identifier - https://github.com/org-trello/org-trello/issues/98
- [X] Fix sync from trello which loses the state of the checkboxes
- [X] Fix tests break since org-trello.el has been destroyed and simplify the testing
- [X] Overload the C-e mapping to go at the end of the line for the org-trello mode
- [X] Update doc
- [X] Release notes

# 0.2.8.2

- [X] Fix yet another error on synchronization from trello.
- [X] Update doc
- [X] Release notes

# 0.2.8.1

- [X] Fix error on synchronization from trello
- [X] Update doc
- [X] Release notes

# 0.2.8

- [X] Backlog
- [X] Synchronize description - https://github.com/org-trello/org-trello/issues/80
- [X] Use --reduce-from from dash instead of cl-reduce to reduce the cl deps
- [X] Version
- [X] Update doc
- [X] Release notes

# 0.2.7

- [X] Backlog
- [X] Create TODO template for the backlog start
- [X] Clean obsolete files (org-trello.org is no longer maintained, TODO-tests.org is no longer used)
- [X] Retry to split into `namespace` files - https://github.com/org-trello/org-trello/issues/93
  - [X] Split into `namespace` files
  - [X] Ensure packaging is generated and ok for marmalade
  - [X] Ensure packaging is generated and ok for melpa - yes, ensure that the root `org-trello.el` is generated before pushing on master.
  - [X] Ensure the tests are still ok
- [X] README-dev - https://github.com/org-trello/org-trello/issues/99
- [X] Rewrite the abstraction around fetched results to unify the `data model` (in and out identical) - https://github.com/org-trello/org-trello/issues/100
- [X] Unify the terms around users-assigned (org-trello) and members (trello)
- [X] Split the last org-trello namespace into 2 (`controller` for the orchestration function call triggered by interactive commands and `org-trello` for the interactive commands)
- [X] Unfold every entries before triggering the sync from trello to avoid problems similar as https://github.com/org-trello/org-trello/issues/53
- [X] Version
- [X] Release notes

# 0.2.6

- [X] Jump to card - https://github.com/org-trello/org-trello/issues/88
- [X] Rewrite convention for the "goto board" action into "jump to board"
- [X] Update README.md
- [X] Version
- [X] Release Note

# 0.2.5

- [X] Backlog updates
- [X] Global properties in upper case - https://github.com/org-trello/org-trello/issues/83
- [X] Hide the global properties - https://github.com/org-trello/org-trello/issues/77
- [X] Use of checkbox convention - https://github.com/org-trello/org-trello/issues/78
- [X] Jumping from emacs to the current trello board - https://github.com/org-trello/org-trello/issues/76
- [X] Simplify the update of the help menu to avoid possible desynchronisation with code
- [X] Update documentation + TOC
- [X] Version
- [X] Release notes

# 0.2.4

- [X] Sprint backlog
- [X] Some refactoring + tests coverage
- [X] Fix sync-from-trello - Merge org card's users assigned list and the trello one
- [X] Fix sync-from-trello - if new entities are referenced but not yet sync'ed on trello, they will disappear from the buffer when sync-from-trello (they should not) - https://github.com/org-trello/org-trello/issues/71
  - [X] Compute the entities without sync'ed properties
  - [X] Write them silly at the end of the computation of the sync'ed data (trello and org merge) to the org buffer
- [X] Upgrade version
- [X] Release notes

# 0.2.3

- [X] Version
- [X] Fix discrepancy between docstring and binding to delete the setup - https://github.com/org-trello/org-trello/issues/74
- [X] Use a prefix binding which does not override the emacs's default user prefix (keep the original for the moment to avoid disturbing people which already use it) - https://github.com/org-trello/org-trello/issues/72
- [X] Update documentation about the possibility to change the default prefix key
- [X] Fix ci-travis build due to change in cask installation command
- [X] Release notes

# 0.2.2

- [X] Version
- [X] Improve abstraction around data from trello (not complete yet)
- [X] Show people assigned to card - https://github.com/org-trello/org-trello/issues/67
  - [X] Compute user properties part from the board's informations
  - [X] Install board setup routine (C-c o I) also install board users
  - [X] Create board routine (C-c o i) should also install user boards (only the current user should then appear)
  - [X] Setuping properties before doing any actions
  - [X] Cleanup routine should also remove user global properties
  - [X] User assigns oneself to the card
  - [X] User unassigns oneself to the card
  - [X] sync-to-trello also assign users
  - [X] sync-to-trello also unassign users
  - [X] sync-from-trello also retrieve user informations and update the org buffer
  - [X] cleanup routine must cleanup card properties regarding user assigned
- [X] Update README about new command
- [X] Update README TOC
- [X] Release notes

# 0.2.1.2

- [X] Version
- [X] Release notes
- [X] Fix typography in naming windows-nt system

# 0.2.1.1

- [X] Version
- [X] Release notes
- [X] Fix error in packaging manipulation

# 0.2.1

- [X] Version
- [X] Improve sync from trello - In case of new item/checklist, the entry will be added at the end of the buffer instead of its rightful place.
- [X] Problem regarding some function on windows system - https://github.com/org-trello/org-trello/issues/62
- [X] Release notes

# 0.2.0

- [X] Version
- [X] Improve cleanup of the org-trello metadata
- [X] Videos about org-trello
  - [X] Webadmin
  - [X] Checkbox
  - [X] Sync from trello
  - [X] Cleanup trello board
  - [X] Cleanup org-trello buffe
- [X] Reference videos to README
- [X] Improve sync to trello
- [X] Release notes

# 0.1.9

- [X] Clean install org-trello
- [X] Ensure sync-from-trello keep the order of the checklists clean
- [X] Version
- [X] Release notes

# 0.1.8

- [X] Simplify Cask file
- [X] webadmin: Improve rendering [2/2]
  - [X] Better display for the delete buttons.
  - [X] Use css for the play/pause entities
- [X] Ensure checks before sync request to the proxy.
- [X] Fix sync full entity (related to map-checkbox) - https://github.com/org-trello/org-trello/issues/53
- [X] Improve the justify policy once and for all (this blinks at the moment!)
- [X] Version
- [X] Fix problem with archive/unarchive file routine
- [X] Fix problem with delete file routine (does not take place)
- [X] Add missing callback for the delete action
- [X] Improve the post-actions
  - [X] Justify once
  - [X] Saving once
  - [X] Unify the saving behaviour with the delete action

# 0.1.7.1

- [X] Fix problem requiring cl-lib - https://github.com/org-trello/org-trello/issues/51
- [X] Fix error on when-let - https://github.com/org-trello/org-trello/issues/54
- [X] Version
- [X] release notes

# 0.1.7

- [X] webadmin: Add an action button on action to stop it
- [X] webadmin: Add an action button to stop every running actions on entities
- [X] URLencode/Protect the data from the query before executing the query - https://github.com/org-trello/org-trello/issues/46
- [X] Some refactoring about:
  - [X] Docstring position (same level as function definition, this way, when toggling sexp, we see the docstring too)
  - [X] Simplification of cond statement
  - [X] Adding some missing tests
  - [X] Simplifying some code function (removing let when not needed)
- [X] Fix the scan problem with level 3 (must have been introduced with the refactoring from number to variable level)
- [X] Remove the marker notion and use the identifier in its place (we already use it as marker)
- [X] Fix the :PROPERTIES: font lock (which is not painted as keyword)
- [X] Improve the justify policy (trim the content before computing the justifying) -> There remains erratic behaviour
- [X] Improve map-checkbox to deal with limit (map over checkbox inferior to current level, at the moment, we scan all checkboxes)
- [X] Version
- [X] Release notes

# 0.1.6

- [X] Use the native org checklist to sync to trello
- [X] Sync entity and arborescence tree
- [X] Sync to trello must sync the native checklist if the flag is activated
- [X] Sync from trello must create native checklists if the flag is activated
- [X] Cleanup routine must cleanup the new checklist.
- [X] Delete entity must remove entity on point
- [X] Upgrade version
- [X] Automate the release to marmalade
- [X] Justify the #PROPERTIES# to the left for a better rendering
- [X] Keywordify the #PROPERTIES#
- [X] Merge the org :PROPERTIES: and the org-trello #PROPERTIES# into one.
- [X] Improve the activation/deactivation of the new way
- [X] Update the readme about the new checkbox mode
- [X] Release notes
- [X] Release

# 0.1.5

- Symmetry in the architecture - the deletion must pass through the consumer too.
- Upgrade version
- webadmin: Improve the rendering of the webadmin page to add headers and action
- webadmin: Add a current scanning entry in the webadmin page
- Defining log level using variable
- Redefine main function to sync an entity (they are badly named).
- Release notes
- Release

# 0.1.4

- Prepare the hierarchy files to avoid problem like https://github.com/org-trello/org-trello/issues/37#issuecomment-23151353
- Adding a version interactive command (it will help for asking people the version they use).
- Upgrade version
- Refactoring - simplify code
- Improve message labels
- Improve failure dealing regarding the sync
- Improve the marker computation
- Remove the label/title notion and use the name notion (same as trello), this will reduce error reasoning.
- Fix the format with missing argument on the callback sync success
- Improve the test regarding the synchro completion of a level
- Order when syncing to trello
- Release notes
- Release

# 0.1.3

- Leverage elnode's webserver capacity to display some basic monitoring about the synchronization
- Install bootstrap and jquery.js directly to avoid the user's manual installation (the first query to static files install bootstrap and jquery now)
- Simple end to end test - simple entity creation
- Improve the logging policy
- Improve the saving policy
- Upgrade version
- Release notes
- Release

# 0.1.2

- DONE Use an intermediary server between org and trello to permit asynchronous actions
- DONE Change org-trello's loading policy + update the readme about it
- DONE Find a way to make the proxy less verbose
- DONE Fix the loss of todo keywords after the synchronization -> no idea what's wrong here
- DONE Improve the attachment board routine to add the missing | keyword (hardcode with DONE for example)
- DONE Improve the clearing of already present heading metadata
- DONE Improve the help message to categorize the bindings
- DONE Improve the starting/stopping of org-trello
- DONE Remove end to end test as this can no longer works with asynchronous
- DONE Update the readme to explain the migration from 0.1.1 to 0.1.2
- DONE Render the sync to trello routine asynchronous
- DONE Render the sync complex entity routine asynchronous
- DONE Render the sync from trello asynchronous
- DONE Fix check setup routine
- DONE Interactive command to cleanup the org-trello data from the current buffer
- DONE Interactive command to delete all entities from the board and the org buffer
- DONE Update version
- DONE Release notes
- DONE Release

# 0.1.1

- DONE Literate org-trello
- DONE Testing the packaging, at the moment, this is done manually (make package & M-x package-install-file)
- DONE Introducing C-c o h at the loading of the buffer when ot is loaded
- DONE Update readme/main page with images on videos
- DONE Replace already present properties regarding boards before injecting new ones.
- DONE Improve the current attach board and list routine to avoid manual setup for the user
- DONE Update version
- DONE Update dependencies lib to more recent version.
- DONE Remove some warnings
- DONE Add some message for the user to warn the user to use UTF-8
- DONE Force utf-8 for the routine of board installation (create aend attach)
- DONE Some more refactoring
- DONE Refactoring: formatting code, install consume-key and access token routine improved, ...
- DONE Refactoring: UTF-8 warning for every routine + Forcing UTF-8 at setup time (create board and attach board routine)
- DONE Refactoring: Adding ^L break line inside the code to delimit the `namespace`
- DONE Refactoring: Improve the callback use by avoiding to specify them
- DONE Refactoring: Restart org-mode after synchronization to avoid losing the user's setup.
- DONE Refactoring: Fix some problems (version, checklist mechanism update, warning on format, create complex entity which sync only the current entity)
- DONE Release notes
- DONE Release

# 0.1.0

- DONE Fix importing of cards with due date - https://github.com/org-trello/org-trello/pull/22
- DONE Migrate carton to card.el (travis-ci builds break because of this)
- DONE Order of creation of list (from keywords) in trello does not match the order of the keyword
- DONE Abstract away the query (:method, :uri, ...) implementation
- DONE Abstract away the implementation of the org-data some more (access of the information from the map are embedded in the function instead of delegating to dedicated function, thus not hiding the implementation)
- DONE Version
- DONE Order when synchronizing from trello does not match trello's order
- DONE Refactor the sync from trello routine function (2 reduce embedded, only one is sufficient)
- DONE Enforce the order of the card accord to the org keywords after dumping the new entries from trello
- DONE Abstract away the return data from the http request
- DONE Update org version to the latest stable
- DONE Release notes

# v0.0.9

- DONE Update videos with the new features in the readme
- DONE Fix bug regarding the saving buffer routine
- DONE Refactoring action code regarding the message to display in the minibuffer (ATM we do not see what is done or not any longer)
- DONE Refactoring the http and http-sync functions
- DONE Improve the delete entity action by forcing the caret to go at the begin of the line of the heading before killing anything.
- DONE Update version
- DONE Release notes

# v0.0.8

- DONE Fix the cl-lib dependency
- DONE Improve the message when an action is done to let the user know when the action is done!
- DONE Better saving buffer policy
- DONE Sync org DEADLINE with trello card due - https://github.com/org-trello/org-trello/issues/17
- DONE Done, Todo on "check lists" - Once the user sets a "check list" to DONE or TODO, then check or uncheck all the tasks it contains. - https://github.com/org-trello/org-trello/issues/16
- DONE A simple and parametrable setup to make the user choose to use the checklist system or not
- DONE Upgrade version
- DONE Release notes
- DONE Release
- DONE Update documentation about deadline, checklist
- DONE Cleanup the debugging functions

# v0.0.7

- DONE Reference missing bindings in documentation
- DONE Upgrade version
- DONE Improve the error message around the setup (the setup message is too generic and must be more detailed)
- DONE Save the buffer after the synchronization is done (after all we write the trello ids in the buffer)
- DONE Release

# v0.0.6.1

- DONE Fix the json-1.3 dependency, sometimes only 1.2 is available
- DONE Update version
- DONE Release

# v0.0.6

- DONE Test that the title/label of the entity is set when syncing to avoid a 400 error
- DONE Before making the request, ensure that everything is ok (checklist needs the card id, items needs the checklist id, etc...)
- DONE Up the demo video in the beginning of the readme
- DONE Improve readme with links to org-mode and trello
- DONE Improve readme's use cases
- DONE Mention the possible errors
- DONE Mention the emacs version
- DONE Update release notes
- DONE Update the version
- DONE Make a release

# v0.0.5

- DONE Synchronizing from the trello board must simply computes and add/remove what's changed [100%]
- DONE Rewrite the release notes in their own file
- DONE Look on how to make a toc in the README.md in github
- DONE Update the release notes
- DONE Release on github, marmalade, melpa

# v0.0.4.1

- DONE Fix the creation board routine regarding the org-mode keywords (dynamic typing hell!)
- DONE Improve documentation regarding the possibilities to setup the org-mode keyword
- DONE Upgrade version to 0.0.4.1
- DONE Release on github, melpa, marmalade

# v0.0.4

- DONE Permit the user to deal with his/her own trello list (based on his/her org-mode keywords - cf. http://orgmode.org/manual/In_002dbuffer-settings.html)
- DONE Deploy on marmalade the stable version (and update the readme about it)
- DONE Rewrite tests using `expectations`
- DONE Simplify some code regarding destructuring for example
- DONE Remove useless code
- DONE Improve documentations and sync the routine check message with the documentation.
- DONE Update documentation
- DONE Release on github, melpa, marmalade

# v0.0.3

- DONE Syncing complex entities
- DONE cleanup useless tests
- DONE Namespace cleanup
- DONE Building package is now able to deal with the right version
- DONE Create a board from org-mode
- DONE Display the name of the board as a property file
- DONE Cleanup the useless controls
- DONE Given a org-mode file, fill in the trello board
- DONE Announce in emacs mailing list
- DONE Filter out the closed boards from the "choose board list"
- DONE filter out level > 4 when syncing.
- DONE Given a trello board, sync into a org-mode file
- cf. [todo/done](./TODO.org) for the remains
- DONE Release on github (and the previous version too)

# v0.0.2

- Technical release fixing technical details
- Fixing the packaging (inlining into org-trello.el)
- Adding ci-travis
- Local packaging to help testing

# v0.0.1

- write only mode at the moment (org-mode pushes to trello, no reading yet)
- simple entity creation (card, checklist, item/task), the request is asynchroneous
- entity deletion (card, checklist, item/task)
- Interactive command to ease the setup of the consumer-key and the access-token
- Interactive command to ease the setup of one org-mode file (which represents one trello board). I assume there exists
  a 'todo', 'doing', and 'done' list (named that way too)
- Control that the setup file (consumer-key and access-token) are rightly generated (to avoid later problem)
- Control that the properties on the current org-mode file are rightly setuped to access a trello board
- packaging for melpa
