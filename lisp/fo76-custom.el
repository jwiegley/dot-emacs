(require 'cl-lib)

(defvar fo76-sort-order
  '("EVB76 - Meshes.ba2"
    "EVB76 - Textures.ba2"
    "CCO76 - Main.ba2"
    "Bombshell_Nuka-Girl - Main.ba2"
    ;; ----
    "InventOmaticPipboy-UO.ba2"
    "InventOmaticStash-UO.ba2"
    "HUDChallenges.ba2"
    "BuffsMeter.ba2"
    "CompatibleWeightIndicator.ba2"))

(defvar fo76-ignore-list
  '("EVB76Nevernude - Meshes.ba2"
    "EVB76Nevernude - Textures.ba2"

    "SeventySix - 00UpdateMain.ba2"
    "SeventySix - 00UpdateTextures.ba2"
    "SeventySix - 00UpdateVoices.ba2"
    "SeventySix - 01UpdateMain.ba2"
    "SeventySix - 01UpdateStream.ba2"
    "SeventySix - 01UpdateTextures.ba2"
    "SeventySix - 01UpdateVoices.ba2"
    "SeventySix - 02UpdateMain.ba2"
    "SeventySix - 02UpdateStream.ba2"
    "SeventySix - 02UpdateTextures.ba2"
    "SeventySix - 02UpdateVoices.ba2"
    "SeventySix - Animations.ba2"
    "SeventySix - EnlightenExteriors01.ba2"
    "SeventySix - EnlightenExteriors02.ba2"
    "SeventySix - EnlightenExteriors03.ba2"
    "SeventySix - EnlightenInteriors01.ba2"
    "SeventySix - EnlightenInteriors02.ba2"
    "SeventySix - GeneratedMeshes01.ba2"
    "SeventySix - GeneratedMeshes02.ba2"
    "SeventySix - GeneratedTextures01.ba2"
    "SeventySix - GeneratedTextures02.ba2"
    "SeventySix - Interface.ba2"
    "SeventySix - Interface_en.ba2"
    "SeventySix - Interface_ja.ba2"
    "SeventySix - Interface_ko.ba2"
    "SeventySix - Interface_ru.ba2"
    "SeventySix - Interface_zhhans.ba2"
    "SeventySix - Interface_zhhant.ba2"
    "SeventySix - Localization.ba2"
    "SeventySix - Materials.ba2"
    "SeventySix - Meshes.ba2"
    "SeventySix - MeshesExtra.ba2"
    "SeventySix - MiscClient.ba2"
    "SeventySix - Shaders.ba2"
    "SeventySix - Sounds01.ba2"
    "SeventySix - Sounds02.ba2"
    "SeventySix - Startup.ba2"
    "SeventySix - StaticMeshes.ba2"
    "SeventySix - Textures01.ba2"
    "SeventySix - Textures02.ba2"
    "SeventySix - Textures03.ba2"
    "SeventySix - Textures04.ba2"
    "SeventySix - Textures05.ba2"
    "SeventySix - Textures06.ba2"
    "SeventySix - Textures07.ba2"
    "SeventySix - Textures08.ba2"
    "SeventySix - Textures09.ba2"
    "SeventySix - Textures10.ba2"
    "SeventySix - Voices.ba2"
    "SeventySix - WorkshopIcons.ba2"))

(defun fo76-archive-files (dir)
  (let (result)
    (dolist (entry (directory-files dir))
      (unless (member entry '("." ".."))
        (let ((path (expand-file-name entry dir)))
          (if (string-match "\\.ba2\\'" path)
              (setq result
                    (cons (file-name-nondirectory path)
                          result))
            (if (file-directory-p path)
                (setq result
                      (nconc result
                             (fo76-archive-files path))))))))
    result))

(defun fo76-compare-archives (x y)
  (let ((x-pos (cl-position x fo76-sort-order :test #'string=))
        (y-pos (cl-position y fo76-sort-order :test #'string=)))
    (if x-pos
        (if y-pos
            (< x-pos y-pos)
          nil)
      (if y-pos
          t
        (string< x y)))))

(defun fo76-sort-archives (archives)
  (cl-stable-sort archives #'fo76-compare-archives))

(defun fo76-sort-custom-ini ()
  (interactive)
  (with-current-buffer
      (find-file "C:\\Users\\jwieg\\OneDrive\\Documents\\My Games\\Fallout 76\\Fallout76Custom.ini")
    (goto-char (point-min))
    (search-forward "sResourceArchive2List=")
    (delete-region (match-end 0) (point-max))
    (insert
     (mapconcat
      #'identity
      (fo76-sort-archives
       (cl-delete-if
        #'(lambda (x) (cl-find x fo76-ignore-list :test #'string=))
        (fo76-archive-files "C:\\Program Files (x86)\\Steam\\steamapps\\common\\Fallout76\\Data")))
      ","))))
