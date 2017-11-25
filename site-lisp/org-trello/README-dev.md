README for the org-trello developer
===================================

<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-generate-toc again -->
**Table of Contents**

- [Sources](#sources)
    - [Conventions](#conventions)
        - [Rules](#rules)
        - [Exception](#exception)
    - [Namespaces](#namespaces)
    - [Loading](#loading)
- [Makefile](#makefile)
    - [Package](#package)
    - [Test](#test)
    - [Install](#install)
    - [Full install testing](#full-install-testing)
    - [Release](#release)

<!-- markdown-toc end -->

This will describe org-trello's current state of affairs.

# Sources

The sources are splitted in `namespaces` in the [src/](./src/) folder.
This is described in the [Namespaces](#namespaces) section.

## Conventions

As there exists no namespace in emacs-lisp, I use:
- convention in function names to determine the nature private/public
- splitted files that represents namespaces.

### Rules

The conventions enforced in org-trello:

- functions are prefixed with `orgtrello-<NAMESPACE-FILENAME>-<FUNCTION-NAME>`
- `<NAMESPACE-FILENAME>` is the filename without its path nor its extension.
For example, `src/buffer.el` renders `buffer`
- `<FUNCTION-NAME>` is an alphanumeric symbol with `-` as separator.
For example, `orgtrello-api-add-board` is a public function which does create a
request to add a board.
- private functions are prefixed with `--`. For example,
`orgtrello-api--deal-with-optional-values` which is a private utility function
to help in creating api request.
- predicate functions are suffixed by `-p`. For example,
`orgtrello-data-entity-card-p` which checks if the parameter entity is a card
or not.

*Note* I adapted the code to abide by [emacs-lisp's conventions](https://www.gnu.org/software/emacs/manual/html_node/elisp/Coding-Conventions.html).

### Exception

`org-trello.el` is the main namespace that declares the:
- interactive commands used throughout all of org-trello
- minor mode

Every exposed interactive command is named `org-trello-fn-name`.

## Namespaces

The namespaces are in loading order:

Namespaces file              | Description of the namespace
-----------------------------|------------------------------------------------------------------------
org-trello-log.el            | Provide log facilities
org-trello-setup.el          | Main variable definition that permits internal
                             |   org-trello functions customization
org-trello-date.el           | org-trello's date manipulation
org-trello-hash.el           | Hash-map manipulation utilities
org-trello-action.el         | Higher-order functions helper
org-trello-data.el           | Internal org-trello data manipulation
org-trello-entity.el         | Entity (card/checklist/item) predicates
org-trello-cbx.el            | Checkbox manipulation utilities
org-trello-api.el            | Trello API abstraction DSL
org-trello-query.el          | HTTP query utilities
org-trello-backend.el        | Deals with trello requests
org-trello-proxy.el          | Proxy utilities - Namespace in charge of dealing
                             | with the orchestration of trello requests
org-trello-buffer.el         | Buffer manipulation functions
org-trello-input.el          | Text input functions
org-trello-controller.el     | Controller used by org-trello.el
org-trello-deferred.el       | Deferred computation in org-trello
org-trello.el                | Main information about org-trello (version,
                             | licence, deps, etc...) + org-trello minor mode
                             | definition which defines interactive commands
                             | and the mode
-----------------------------|-------------------------------------------------------------------------
utilities.el                 | test utilities functions

## Loading

Use the [load-org-trello.el](./load-org-trello.el) file to load org-trello for
development purposes and keep the emacs way of browsing source code
(`M-.`, `M-,`).

Open the file and `M-x eval-buffer`.

# Makefile

the [Makefile](./Makefile) is your ally for:
- package
- test
- release

## Package

This packages all the /org-trello*.el/ into a standard tar file.

```sh
make package
```

## Test

```sh
make test
```

## Install

To test that the package, once created, can be installed (using the repository
to fetch the dependencies).

```sh
make install-file-with-deps-from-melpa
```

*Note*:
This will trigger the installation from a local package `org-trello-<VERSION>.tar`.
The installation is used with the dependencies fetched from melpa.

*Note 2*
These are the targets used by the CI (cf. [.travis.yml](./.travis.yml))

## Full install testing

As we deploy in melpa, we can ensure that once delivered, the installation is ok
using those targets.

```sh
make install-package-from-melpa
```

## Release

The release process is done through 2 steps:
- Self Pull Request from the feature branch inside master

    ```sh
    make pr
    ```

    *Note* You need `hub` installed for this target to work.

- Then trigger release through the call to the release target from the Makefile

    ```sh
    make release
    ```

This will:
- fetch the latest modifications on your repository
- checkout the master branch
- fast-forward to the latest master commit
- tag the latest commit from master using the $VERSION you submit to the script
(defaulting to the version from the org-trello.el header)
- push the tag to the upstream branch repository
- trigger the package target from the Makefile (thus building a new package to
the latest version)
- Then manual delivery of the tar to the github release page

Note:
- this is an orchestration of the [release.sh](./release.sh) script
- the packaging for MELPA is automatically done from `org-trello/org-trello`
repository
