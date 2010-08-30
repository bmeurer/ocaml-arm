;(***********************************************************************)
;(*                                                                     *)
;(*                           Objective Caml                            *)
;(*                                                                     *)
;(*            Didier Remy, projet Cristal, INRIA Rocquencourt          *)
;(*                                                                     *)
;(*  Copyright 2003 Institut National de Recherche en Informatique et   *)
;(*  en Automatique.  All rights reserved.  This file is distributed    *)
;(*  under the terms of the GNU General Public License.                 *)
;(*                                                                     *)
;(***********************************************************************)

;(* $Id$ *)

(require 'overlay)

;; for caml-help.el
(defun caml-info-other-window (arg)
  (save-excursion (info arg))
  (view-buffer-other-window "*info*"))

;; for caml-types.el
(defun caml-line-beginning-position ()
  (save-excursion (beginning-of-line) (point)))

(defalias 'caml-read-event 'next-event)
(defalias 'caml-window-edges 'window-pixel-edges)
(defun caml-mouse-vertical-position ()
  (let ((e  (mouse-position-as-motion-event)))
    (and e (event-y-pixel e))))
(defalias 'caml-mouse-movement-p 'motion-event-p)
(defun caml-event-window (e)
  (and (mouse-event-p e) (event-window e)))
(defun caml-event-point-start (e) (event-closest-point e))
(defun caml-event-point-end (e) (event-closest-point e))
(defun caml-ignore-event-p (e)
  (if (and (key-press-event-p e) (equal (key-binding e) 'keyboard-quit))
      (keyboard-quit))
  (not (mouse-event-p e)))


(defun caml-sit-for (sec &optional mili)
  (sit-for (+ sec (if mili (* 0.001 mili) 0))))



(defmacro caml-track-mouse (&rest body) (cons 'progn body))

(defun caml-release-event-p (original event)
  (and (button-release-event-p event)
       (equal (event-button original) (event-button event))))

(defun caml-string-to-int (x)
  (if (fboundp 'string-to-number) (string-to-number x) (string-to-int x)))

(provide 'caml-xemacs)
