(set-fontset-font t '(#x2113 . #x2113) (font-spec :family "noto"))

(defvar absint-symbols
  (prettify-utils-generate ("\\pgmset" "ℙ")
                           ("\\pgm" "𝖯")
                           ("\\pgmcmp" "ℙ𝕔")
                           ("\\stmtlistset" "𝕊𝕝")
                           ("\\stmtset" "𝕊")
                           ("\\tracevalues" "𝕍")
                           ("\\traceactions" "𝔸𝕔𝕥")
                           ("\\tracevalue" "𝓋")
                           ("\\traceaction" "𝚊")
                           ("\\trace" "𝕋")
                           ("\\tracearrow" "→")
                           ("\\traceconcat" "𝄐")
                           ("\\environments" "𝔼𝕧")
                           ;; A compromise -- doublestruck
                           ;; italic is often unavailable in font inventories
                           ("\\aeval" "𝒜")
                           ("\\beval" "𝓑")
                           ("\\variables" "𝕍𝕒𝕣")
                           ("\\semantic" "𝒮")
                           ("\\ell" "ℓ")
                           ("\\stmt" "𝖲")
                           ("\\aexpr" "𝖠")
                           ("\\bexpr" "𝖡")
                           ("\\stmtlist" "𝖲𝗅")
                           ("\\true" "𝗍𝗍")
                           ("\\false" "𝖿𝖿")
                           ("\\llbracket" "⟦")
                           ("\\rrbracket" "⟧")
                           ("\\Lbag" "⟅")
                           ("\\Rbag" "⟆")
                           ("\\synif" "𝗂𝖿")
                           ("\\synelse" "𝖾𝗅𝗌𝖾")
                           ("\\synwhile" "𝗐𝗁𝗂𝗅𝖾")
                           ("\\synbreak" "𝖻𝗋𝖾𝖺𝗄;")
                           ("\\synvar" "𝗑")
                           ("\\pcat" "at")
                           ("\\pcafter" "after")
                           ("\\pcescape" "escape")
                           ("\\pcbreakto" "break-to")
                           ("\\pcbreaksof" "breaks-of")
                           ("\\pcin" "in")
                           ("\\pclabs" "labs")
                           ("\\pclabx" "labx")
                           ("\\emptytrace" "∋")
                           ("\\synassign" "=")
                           ("\\synskip" ";")
                           ("\\lbl" "ℓ")
                           ("\\emptysl" "𝞊")
                           ("\\llparenthesis" "⦇")
                           ("\\rrparenthesis" "⦈")
                           ("\\traces" "𝒯")
                           ("\\definiendum" "D")
                           ("\\universe" "𝕌")
                           ("\\increasing" "→↗")
                           ("\\lfp" "lfp")
                           ("\\abs" "𝒜")
                           ("\\crc" "𝒞")
                           ("\\preproperty" "ℙ")
                           ("\\postproperty" "ℚ")
                           ("\\post" "post")
                           ("\\dpost" "pôst")
                           ("\\tojoin" "→⊔")
                           ("\\tomeet" "→⊓")
                           )
  "Abstract interpretaion symbols for use in latex")

(defun absint-brackets ()
  (interactive)
  (TeX-add-symbols
   '("Lbag" TeX-arg-insert-right-brace-maybe)
   '("llbracket" TeX-arg-insert-right-brace-maybe)
   "Rbag"
   "rrbracket"))

(defun absint-prettify ()
  (interactive)
  (setq prettify-symbols-alist (append absint-symbols prettify-symbols-alist)))

(push 'absint-prettify LaTeX-mode-hook)
(push 'absint-brackets LaTeX-mode-hook)

;; parens:

(sp-with-modes '(
                 tex-mode
                 plain-tex-mode
                 latex-mode
                 LaTeX-mode
                 )
  (sp-local-pair  "\\Lbag" "\\Rbag "
          :when '(sp-in-math-p)
          :trigger "\\Lbag"
          :post-handlers '(sp-latex-insert-spaces-inside-pair))
  (sp-local-pair  "\\llparenthesis" "\\rrparenthesis"
          :when '(sp-in-math-p)
          :trigger "\\llparenthesis"
          :post-handlers '(sp-latex-insert-spaces-inside-pair))
  (sp-local-pair  "\\llbracket" "\\rrbracket"
          :when '(sp-in-math-p)
          :trigger "\\llbracket"
          :post-handlers '(sp-latex-insert-spaces-inside-pair)))
