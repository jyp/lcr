;;; lcc.el  -*- lexical-binding: t -*-

;;; Copyright (C) 2015-2016 Free Software Foundation, Inc.

;; Author: Daniel Colascione <dancol@dancol.org>
;; Keywords: extensions, elisp




(defun lcc-call (fun &rest args)
  (error "`lcc-call' used outside a co-routine"))

(defvar lcc--yield-seen)
(setq lcc-inhibit-atomic-optimization t)
(defun lcc--atomic-p (form)
  "Return whether the given form never yields."

  (and (not lcc-inhibit-atomic-optimization)
       (let* ((lcc-yield-seen))
         (ignore (macroexpand-all
                  `(cl-macrolet ((lcc-call (fun &rest args) (setf lcc-yield-seen t)))
                     ,form)
                  macroexpand-all-environment))
         (not lcc-yield-seen))))


(lcc--transform-1 ''example (lambda (x) x))
(lcc--transform-1 '(and a b) (lambda (x) x))
(lcc--transform-1 '(progn (if a b c) d) (lambda (x) x))
(lcc--transform-1 '(progn a b c d) (lambda (x) x))
(lcc--transform-1 '(if a b c d) (lambda (x) x))
(lcc--transform-1 '(if a (and e f) c d) (lambda (x) x))
(lcc--transform-1 '(let () aowfutn) (lambda (x) x))
(lcc--transform-1 '(let ((x yop)) (and a b)) (lambda (x) x))
(lcc--transform-1 '(let* ((x yop)) (and a b)) (lambda (x) x))
(lcc--transform-1 '(or) (lambda (x) x))
(lcc--transform-1 '(or a) (lambda (x) x))
(lcc--transform-1 '(or a b) (lambda (x) x))
(lcc--transform-1 '(prog1 a b c) (lambda (x) x))
(lcc--transform-1 '(prog2 a b c) (lambda (x) x))

(lcc--transform-n '(x y z) (lambda (xs) xs))
(lcc--transform-n '() (lambda (xs) xs))


(defun lcc--transform-n (forms k)
  "Transform FORMS and pass the results to K."
  (pcase forms
    (`() (funcall k ()))
    (`(,form . ,rest) (lcc--transform-1 form (lambda (x) (lcc--transform-n rest (lambda (xs) (funcall k (cons x xs)))))))
  ))

(defun lcc--transform-1 (form k)
  "Transform FORM and pass the result to K."
  (pcase form
    ;; ((guard (lcc--atomic-p form))
    ;; (let (x (cl-gensym))
    ;;  `(let ((,x ,form)) ,(funcall k x))))

    ((guard (atom form)) (funcall k form))

    ;; Process `and'.
    (`(and) (funcall k 't))
    (`(and ,condition)                  ; (and CONDITION) -> CONDITION
      (lcc--transform-1 condition k))
    (`(and ,condition . ,rest)
      (lcc--transform-1 condition
                        (lambda (x)
                          `(if ,x ,(lcc--transform-1 `(and ,@rest) k)
                             ,(funcall k 'nil)))))
    (`(cond)                            ; (cond) -> nil
      (lcc--transform-1 nil k))
    (`(cond (,condition) . ,rest)
     (lcc--transform-1 `(or ,condition (cond ,@rest)) k))
    (`(cond (,condition . ,body) . ,rest)
     (lcc--transform-1 `(if ,condition
                            (progn ,@body)
                          (cond ,@rest))
                       k))
    (`(cond (,condition) . ,rest)
      (lcc--transform-1 `(or ,condition (cond ,@rest))
                        next-state))
    (`(cond (,condition . ,body) . ,rest)
      (lcc--transform-1 `(if ,condition
                             (progn ,@body)
                           (cond ,@rest))
                        next-state))

    ;; Process `if'.

    (`(if ,cond ,then . ,else)
      (lcc--transform-1 cond
                        (lambda (c)
                          `(if ,c
                               ,(lcc--transform-1 then k)
                             ,(lcc--transform-1 `(progn ,@else) k)))))

    ;; Process `progn' and `inline': they are identical except for the
    ;; name, which has some significance to the byte compiler.

    (`(inline) (lcc--transform-1 nil k))
    (`(inline ,form) (lcc--transform-1 form k))
    (`(inline ,form . ,rest)
     (lcc--transform-1 form
                       (lambda (_) (lcc--transform-1 `(inline ,@rest)
                                         k))))

    (`(progn) (lcc--transform-1 nil k))
    (`(progn ,form) (lcc--transform-1 form k))
    (`(progn ,form . ,rest)
     (lcc--transform-1 form
                       (lambda (_) (lcc--transform-1 `(progn ,@rest)
                                         k))))

    (`(let ,bindings . ,body)
     (lcc--transform-n (-map #'cadr bindings)
                       (lambda (xs) `(let ,(-zip-with 'list (-map #'car bindings) xs)
                                       ,(lcc--transform-1 `(progn ,@body) k)))))
    (`(let* () . ,body)
      (lcc--transform-1 `(progn ,@body) k))
    (`(let* ((,var ,value-form) . ,more-bindings) . ,body)
        (lcc--transform-1
         value-form
         (lambda (x) `(let* ((,var ,x)) ,(lcc--transform-1 `(let* ,more-bindings ,@body) k)))))
    ;; Process `or'.
    (`(or) (lcc--transform-1 'nil k))
    (`(or ,condition) (lcc--transform-1 condition k))
    (`(or ,condition . ,rest)
      (lcc--transform-1 condition
                        (lambda (x)
                          `(if ,x
                              ,(funcall k x)
                            ,(lcc--transform-1
                              `(or ,@rest) k)))))
    ;; Process `prog1'.
    (`(prog1 ,first) (lcc--transform-1 first k))
    (`(prog1 ,first . ,body)
      (lcc--transform-1
       first (lambda (x) (lcc--transform-1 `(progn ,@body) (lambda (_) (funcall k x))))))
    ;; Process `prog2'.
    (`(prog2 ,form1 ,form2 . ,body)
      (lcc--transform-1 `(progn ,form1 (prog1 ,form2 ,@body)) k))
    ;; Process `while'.
    (`(while ,test . ,body)
     (let ((while-fun (cl-gensym "while")))
       ;; [while c body]k --> (flet (loop () [c]λx.(if x ([body]λy. (loop) (k nil))) )
      ;; Open-code state addition instead of using cps--add-state: we
      ;; need our states to be self-referential. (That's what makes the
      ;; state a loop.)
       `(flet ((,while-fun ()
                ,(lcc--transform-1
                  test
                  (lambda (x) `(if ,x ,(lcc--transform-1 `(progn ,@body) (lambda (_) `(,while-fun))) ,(funcall k 'nil))))))
          (,while-fun))))
    ;; Process various kinds of `quote'.
    (`(quote ,arg) (funcall k `(quote ,arg)))
    (`(function ,arg) (funcall k `(function ,arg)))
    (`(lcc-internal-call . (,fun . ,args))
     (let ((var (cl-gensym "v")))
       (lcc--transform-1 fun (lambda (f)
                               (lcc--transform-n args (lambda (xs)
                                                        `((,fun ,@xs (lambda (,var) ,(funcall k var))))))))))
    (`(,fun . ,args )
     (let ((var (cl-gensym "v")))
       (lcc--transform-1 fun (lambda (f)
                               (lcc--transform-n args (lambda (xs)
                                                        `(let ((,var (,fun ,@xs))) ,(funcall k var))))))))
    ))


(lcc--transform-1 '(while c a) (lambda (x) x))
(lcc--transform-1 '(quote quote) (lambda (x) x))
(lcc--transform-1 '(f x y) (lambda (x) x))



    
    (`(function ,arg) (cps--add-state "function"
                        `(setf ,cps--value-symbol (function ,arg)
                               ,cps--state-symbol ,next-state)))

    ;; Deal with `iter-yield'.

    (`(lcc-internal-call ,fun . ,args )
      (lcc--transform-1
       value
       (cps--add-state "iter-yield"
         `(progn
            (setf ,cps--state-symbol
                  ,(if cps--cleanup-function
                       (cps--add-state "after-yield"
                         `(setf ,cps--state-symbol ,next-state))
                       next-state))
            (throw 'cps--yield ,cps--value-symbol)))))

    ;; Catch any unhandled special forms.

    ((and `(,name . ,_)
          (guard (cps--special-form-p name))
          (guard (not (memq name cps-standard-special-forms))))
     name                               ; Shut up byte compiler
     (error "special form %S incorrect or not supported" form))

    ;; Process regular function applications with nontrivial
    ;; parameters, converting them to applications of trivial
    ;; let-bound parameters.

    ((and `(,function . ,arguments)
          (guard (not (cl-loop for argument in arguments
                         always (atom argument)))))
     (let ((argument-symbols
            (cl-loop for argument in arguments
               collect (if (atom argument)
                           argument
                         (cps--gensym "cps-argument-")))))

       (lcc--transform-1
        `(let* ,(cl-loop for argument in arguments
                   for argument-symbol in argument-symbols
                   unless (eq argument argument-symbol)
                   collect (list argument-symbol argument))
           ,(cons function argument-symbols))
        next-state)))

    ;; Process everything else by just evaluating the form normally.
    (_ (cps--make-atomic-state form next-state))))
