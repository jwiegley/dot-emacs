;;; js3-externs.el -- external name definitions

(defvar js3-ecma-262-externs
  (mapcar 'symbol-name
          '(Array
            Boolean
            Date
            Error
            EvalError
            Function
            Infinity
            JSON
            Math
            NaN
            Number
            Object
            RangeError
            ReferenceError
            RegExp
            String
            SyntaxError
            TypeError
            URIError
            arguments
            decodeURI
            decodeURIComponent
            encodeURI
            encodeURIComponent
            escape
            eval
            isFinite
            isNaN
            parseFloat
            parseInt
            undefined
            unescape))
  "Ecma-262 externs.  Included in `js3-externs' by default.")

(defvar js3-browser-externs
  (mapcar 'symbol-name
          '(;; DOM level 1
            Attr
            CDATASection
            CharacterData
            Comment
            DOMException
            DOMImplementation
            Document
            DocumentFragment
            DocumentType
            Element
            Entity
            EntityReference
            ExceptionCode
            NamedNodeMap
            Node
            NodeList
            Notation
            ProcessingInstruction
            Text

            ;; DOM level 2
            HTMLAnchorElement
            HTMLAppletElement
            HTMLAreaElement
            HTMLBRElement
            HTMLBaseElement
            HTMLBaseFontElement
            HTMLBodyElement
            HTMLButtonElement
            HTMLCollection
            HTMLDListElement
            HTMLDirectoryElement
            HTMLDivElement
            HTMLDocument
            HTMLElement
            HTMLFieldSetElement
            HTMLFontElement
            HTMLFormElement
            HTMLFrameElement
            HTMLFrameSetElement
            HTMLHRElement
            HTMLHeadElement
            HTMLHeadingElement
            HTMLHtmlElement
            HTMLIFrameElement
            HTMLImageElement
            HTMLInputElement
            HTMLIsIndexElement
            HTMLLIElement
            HTMLLabelElement
            HTMLLegendElement
            HTMLLinkElement
            HTMLMapElement
            HTMLMenuElement
            HTMLMetaElement
            HTMLModElement
            HTMLOListElement
            HTMLObjectElement
            HTMLOptGroupElement
            HTMLOptionElement
            HTMLOptionsCollection
            HTMLParagraphElement
            HTMLParamElement
            HTMLPreElement
            HTMLQuoteElement
            HTMLScriptElement
            HTMLSelectElement
            HTMLStyleElement
            HTMLTableCaptionElement
            HTMLTableCellElement
            HTMLTableColElement
            HTMLTableElement
            HTMLTableRowElement
            HTMLTableSectionElement
            HTMLTextAreaElement
            HTMLTitleElement
            HTMLUListElement

            ;; DOM level 3
            DOMConfiguration
            DOMError
            DOMException
            DOMImplementationList
            DOMImplementationSource
            DOMLocator
            DOMStringList
            NameList
            TypeInfo
            UserDataHandler

            ;; Window
            window
            alert
            confirm
            document
            java
            navigator
            prompt
            screen
            self
            top

            ;; W3C CSS
            CSSCharsetRule
            CSSFontFace
            CSSFontFaceRule
            CSSImportRule
            CSSMediaRule
            CSSPageRule
            CSSPrimitiveValue
            CSSProperties
            CSSRule
            CSSRuleList
            CSSStyleDeclaration
            CSSStyleRule
            CSSStyleSheet
            CSSValue
            CSSValueList
            Counter
            DOMImplementationCSS
            DocumentCSS
            DocumentStyle
            ElementCSSInlineStyle
            LinkStyle
            MediaList
            RGBColor
            Rect
            StyleSheet
            StyleSheetList
            ViewCSS

            ;; W3C Event
            EventListener
            EventTarget
            Event
            DocumentEvent
            UIEvent
            MouseEvent
            MutationEvent
            KeyboardEvent

            ;; W3C Range
            DocumentRange
            Range
            RangeException

            ;; W3C XML
            XPathResult
            XMLHttpRequest
            ))
  "Browser externs.
You can cause these to be included or excluded with the custom
variable `js3-include-browser-externs'.")

(defvar js3-rhino-externs
  (mapcar 'symbol-name
          '(Packages
            importClass
            importPackage
            com
            org
            java

            ;; Global object (shell) externs
            defineClass
            deserialize
            doctest
            gc
            help
            load
            loadClass
            print
            quit
            readFile
            readUrl
            runCommand
            seal
            serialize
            spawn
            sync
            toint32
            version))
  "Mozilla Rhino externs.
Set `js3-include-rhino-externs' to t to include them.")

(defvar js3-gears-externs
  (mapcar 'symbol-name
          '(
            ;; finish me!
            ))
  "Google Gears externs.
Set `js3-include-gears-externs' to t to include them.")

(provide 'js3-externs)

;;; js3-externs.el ends here
