;;
;;   -- init-file for Xemacs Emacs for Isabelle environment
;;
;;   Franz Regensburger <regensbu@informatik.tu-muenchen.de>
;;   

;;; Isabelle-Font as default
;;(set-default-font "isabelle14")
;;(set-face-font 'default "isabelle14")

;;   activate 8bit chars 
;;   ...for all new buffers
(setq default-ctl-arrow "z")
;;   ...and for the still active buffer
(setq ctl-arrow "z")

;; popup menu for Isabelle fonts

(defun isabelle-fonts-menu (e)
  "Pops up the Isabelle fonts menu."
  (interactive "@e")
  (popup-menu
  '("Isabelle fonts menu"
    ["Isabelle 14" (set-face-font 'default "isabelle14") t]
    ["Isabelle 24" (set-face-font 'default "isabelle24") t]
  )))

(global-unset-key '(shift control button3))
(global-set-key '(shift control button3) 'isabelle-fonts-menu)


;; DO NOT EDIT the lines between BEGIN-KEY-MAP and END-KEY-MAP
;; the table is generated by the perl script `gen-isa_xemacs'
;; In order to make changes to the keyboard mappings you should edit
;; the configuration file `key-table.inp' which is interpreted by
;; the perl script `gen-isa_xemacs', 
;;
;;
;; key-map for Isabelle font
;;   
;; BEGIN-KEY-MAP
(global-set-key '(super G) '(lambda () (interactive) (insert "\241")))
(global-set-key '(super D) '(lambda () (interactive) (insert "\242")))
(global-set-key '(super J) '(lambda () (interactive) (insert "\243")))
(global-set-key '(super L) '(lambda () (interactive) (insert "\244")))
(global-set-key '(super P) '(lambda () (interactive) (insert "\245")))
(global-set-key '(super S) '(lambda () (interactive) (insert "\246")))
(global-set-key '(super F) '(lambda () (interactive) (insert "\247")))
(global-set-key '(super Q) '(lambda () (interactive) (insert "\250")))
(global-set-key '(super W) '(lambda () (interactive) (insert "\251")))
(global-set-key '(super a) '(lambda () (interactive) (insert "\252")))
(global-set-key '(super b) '(lambda () (interactive) (insert "\253")))
(global-set-key '(super g) '(lambda () (interactive) (insert "\254")))
(global-set-key '(super d) '(lambda () (interactive) (insert "\255")))
(global-set-key '(super e) '(lambda () (interactive) (insert "\256")))
(global-set-key '(super z) '(lambda () (interactive) (insert "\257")))
(global-set-key '(super h) '(lambda () (interactive) (insert "\260")))
(global-set-key '(super j) '(lambda () (interactive) (insert "\261")))
(global-set-key '(super k) '(lambda () (interactive) (insert "\262")))
(global-set-key '(super l) '(lambda () (interactive) (insert "\263")))
(global-set-key '(super m) '(lambda () (interactive) (insert "\264")))
(global-set-key '(super n) '(lambda () (interactive) (insert "\265")))
(global-set-key '(super x) '(lambda () (interactive) (insert "\266")))
(global-set-key '(super p) '(lambda () (interactive) (insert "\267")))
(global-set-key '(super r) '(lambda () (interactive) (insert "\270")))
(global-set-key '(super s) '(lambda () (interactive) (insert "\271")))
(global-set-key '(super t) '(lambda () (interactive) (insert "\272")))
(global-set-key '(super f) '(lambda () (interactive) (insert "\273")))
(global-set-key '(super c) '(lambda () (interactive) (insert "\274")))
(global-set-key '(super q) '(lambda () (interactive) (insert "\275")))
(global-set-key '(super w) '(lambda () (interactive) (insert "\276")))
(global-set-key '(hyper n) '(lambda () (interactive) (insert "\277")))
(global-set-key '(hyper a) '(lambda () (interactive) (insert "\300")))
(global-set-key '(hyper o) '(lambda () (interactive) (insert "\301")))
(global-set-key '(hyper f) '(lambda () (interactive) (insert "\302")))
(global-set-key '(hyper t) '(lambda () (interactive) (insert "\303")))
(global-set-key '(hyper F) '(lambda () (interactive) (insert "\304")))
(global-set-key '(control f5) '(lambda () (interactive) (insert "\305")))
(global-set-key '(control f6) '(lambda () (interactive) (insert "\306")))
(global-set-key '(control f7) '(lambda () (interactive) (insert "\307")))
(global-set-key '(control f8) '(lambda () (interactive) (insert "\310")))
(global-set-key '(control f9) '(lambda () (interactive) (insert "\311")))
(global-set-key '(control f10) '(lambda () (interactive) (insert "\312")))
(global-set-key '(control f11) '(lambda () (interactive) (insert "\313")))
(global-set-key '(control f12) '(lambda () (interactive) (insert "\314")))
(global-set-key '(hyper f5) '(lambda () (interactive) (insert "\317")))
(global-set-key '(hyper f6) '(lambda () (interactive) (insert "\371")))
(global-set-key '(hyper f7) '(lambda () (interactive) (insert "\372")))
(global-set-key '(hyper f1) '(lambda () (interactive) (insert "\320")))
(global-set-key '(hyper f2) '(lambda () (interactive) (insert "\321")))
(global-set-key '(hyper f3) '(lambda () (interactive) (insert "\322")))
(global-set-key '(hyper f4) '(lambda () (interactive) (insert "\323")))
(global-set-key '(control f1) '(lambda () (interactive) (insert "\324")))
(global-set-key '(control f2) '(lambda () (interactive) (insert "\325")))
(global-set-key '(control f3) '(lambda () (interactive) (insert "\326")))
(global-set-key '(control f4) '(lambda () (interactive) (insert "\327")))
(global-set-key '(hyper b) '(lambda () (interactive) (insert "\330")))
(global-set-key '(hyper e) '(lambda () (interactive) (insert "\331")))
(global-set-key '(hyper E) '(lambda () (interactive) (insert "\332")))
(global-set-key '(hyper u) '(lambda () (interactive) (insert "\333")))
(global-set-key '(hyper p) '(lambda () (interactive) (insert "\334")))
(global-set-key '(hyper P) '(lambda () (interactive) (insert "\335")))
(global-set-key '(hyper l) '(lambda () (interactive) (insert "\336")))
(global-set-key '(hyper L) '(lambda () (interactive) (insert "\337")))
(global-set-key '(hyper g) '(lambda () (interactive) (insert "\340")))
(global-set-key '(hyper G) '(lambda () (interactive) (insert "\341")))
(global-set-key '(hyper s) '(lambda () (interactive) (insert "\342")))
(global-set-key '(hyper S) '(lambda () (interactive) (insert "\343")))
(global-set-key '(shift f11) '(lambda () (interactive) (insert "\344")))
(global-set-key '(shift f12) '(lambda () (interactive) (insert "\345")))
(global-set-key '(super f1) '(lambda () (interactive) (insert "\346")))
(global-set-key '(super f2) '(lambda () (interactive) (insert "\347")))
(global-set-key '(super f3) '(lambda () (interactive) (insert "\350")))
(global-set-key '(shift f1) '(lambda () (interactive) (insert "\351")))
(global-set-key '(shift f2) '(lambda () (interactive) (insert "\352")))
(global-set-key '(shift f3) '(lambda () (interactive) (insert "\353")))
(global-set-key '(super f5) '(lambda () (interactive) (insert "\354")))
(global-set-key '(super f6) '(lambda () (interactive) (insert "\355")))
(global-set-key '(super f7) '(lambda () (interactive) (insert "\356")))
(global-set-key '(super f8) '(lambda () (interactive) (insert "\357")))
(global-set-key '(super f9) '(lambda () (interactive) (insert "\360")))
(global-set-key '(super f10) '(lambda () (interactive) (insert "\315")))
(global-set-key '(hyper x) '(lambda () (interactive) (insert "\362")))
(global-set-key '(shift f5) '(lambda () (interactive) (insert "\363")))
(global-set-key '(shift f6) '(lambda () (interactive) (insert "\364")))
(global-set-key '(shift f7) '(lambda () (interactive) (insert "\365")))
(global-set-key '(shift f8) '(lambda () (interactive) (insert "\366")))
(global-set-key '(shift f9) '(lambda () (interactive) (insert "\367")))
(global-set-key '(shift f10) '(lambda () (interactive) (insert "\370")))
(global-set-key '(super f11) '(lambda () (interactive) (insert "\316")))
(global-set-key '(super f12) '(lambda () (interactive) (insert "\361")))
(global-set-key '(hyper f8) '(lambda () (interactive) (insert "\373")))
(global-set-key '(hyper f9) '(lambda () (interactive) (insert "\374")))
(global-set-key '(hyper f10) '(lambda () (interactive) (insert "\375")))
(global-set-key '(hyper f11) '(lambda () (interactive) (insert "\376")))
(global-set-key '(hyper f12) '(lambda () (interactive) (insert "\377")))
(global-set-key '(shift f4) '(lambda () (interactive) (insert "\351")(insert "\353")))
(global-set-key '(super f4) '(lambda () (interactive) (insert "\346")(insert "\350")))
(global-set-key '(hyper i) '(lambda () (interactive) (insert "\347")(insert "\350")))
(global-set-key '(hyper I) '(lambda () (interactive) (insert "\352")(insert "\353")))
(global-set-key '(hyper m) '(lambda () (interactive) (insert "\350")))
(global-set-key '(hyper M) '(lambda () (interactive) (insert "\353")))
(global-set-key '(hyper N) '(lambda () (interactive) (insert "\367")))
(global-set-key '(f9) '(lambda () (interactive) (insert "\304")))
(global-set-key '(f10) '(lambda () (interactive) (insert "\352")(insert "\353")))
(global-set-key '(f11) '(lambda () (interactive) (insert "\332")))
(global-set-key '(f12) '(lambda () (interactive) (insert "\333")))
;; END-KEY-MAP





