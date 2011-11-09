;;; emacs -l env.el
(setq
 coq-prog-args (list
		"-R" (expand-file-name "../tools/ynot/ynot/src/coq") "Ynot"
		"-R" (expand-file-name "../tools/ynot/ynot/examples/Data") "Data"
		))
