;;; lcr.el  -*- lexical-binding: t -*-

;; Lightweight coroutines.

;;; Copyright (C) 2018 Jean-Philippe Bernardy.

;; With parts copied from the work of Daniel Colascione
;; <dancol@dancol.org> on generators.

(require 'dash)

;;; Code:

(defun lcr-call (fun &rest args)
  "Call the coroutine FUN with arguments ARGS."
  (error "`lcr-call' used outside a co-routine (%S %S)" fun args))

(defvar lcr--yield-seen)
(defconst lcr-inhibit-atomic-optimization t)
(defun lcr--atomic-p (form)
  "Return whether the given FORM never jumps to another coroutine."
  (and (not lcr-inhibit-atomic-optimization)
       (let* ((lcr-yield-seen))
         (ignore (macroexpand-all
                  `(cl-macrolet ((lcr-call (fun &rest args) (setf lcr-yield-seen t)))
                     ,form)
                  macroexpand-all-environment))
         (not lcr-yield-seen))))

(defmacro def-lcr (name arglist &rest body)
  "Define a lightweight coroutine with NAME, ARGLIST and BODY."
  (declare (indent 2))
  `(progn
     (put ,name 'lcr? t)
     (defun ,name ,(-snoc  arglist 'lcr--continuation)
       ,(lcr--transform-1 `(progn ,@body) (lambda (x) `(funcall lcr--continuation ,x))))))

(defmacro lcr-async-bind (var expr &rest body)
  "Bind VAR in a continuation passed to EXPR with contents BODY.
EXPR is turned to a co-routine but BODY is executed in direct
style (but only after EXPR returns)."
  (declare (indent 2))
  (lcr--transform-1 expr `(lambda (,var) ,@body)))

(defmacro lcr-async-let (bindings &rest body)
"Expand multiple BINDINGS and call BODY as a continuation."
  (declare (indent 2))
  (pcase bindings
    (`((,vars ,expr)) `(lcr-async-bind ,vars ,expr ,@body))
    (`((,vars ,expr) . ,rest) `(lcr-async-bind ,vars ,expr (lcr-async-let ,rest ,@body)))))


(defun lcr--transform-body (forms k)
  "Transform FORMS and pass the result of the last form to K."
  (lcr--transform-1 `(progn ,@forms) k))

(defun lcr--transform-n (forms k)
  "Transform FORMS and pass all the results, as a list, to K."
  (pcase forms
    (`() (funcall k ()))
    (`(,form . ,rest)
     (lcr--transform-1
      form
      (lambda (x) (lcr--transform-n rest (lambda (xs) (funcall k (cons x xs)))))))))

;; see cps--transform-1 for all possible forms.
(defun lcr--transform-1 (form k)
  "Transform FORM and pass the result to K."
  (pcase form
    ;; Process atomic expressions.
    ((guard (lcr--atomic-p form))
     (let (x (cl-gensym "atom"))
       `(let ((,x ,form)) ,(funcall k x))))

    ((guard (atom form)) (funcall k form))

    ;; Process `and'.
    (`(and) (funcall k 't))
    (`(and ,condition)
      (lcr--transform-1 condition k))
    (`(and ,condition . ,rest)
      (lcr--transform-1
       condition
       (lambda (x)
         `(if ,x ,(lcr--transform-1 `(and ,@rest) k)
            ,(funcall k 'nil)))))
    ;; Process `cond'.
    (`(cond)
      (lcr--transform-1 nil k))
    (`(cond (,condition) . ,rest)
     (lcr--transform-1 `(or ,condition (cond ,@rest)) k))
    (`(cond (,condition . ,body) . ,rest)
     (lcr--transform-1 `(if ,condition
                            (progn ,@body)
                          (cond ,@rest))
                       k))
    (`(cond (,condition) . ,rest)
      (lcr--transform-1 `(or ,condition (cond ,@rest))
                        next-state))
    (`(cond (,condition . ,body) . ,rest)
      (lcr--transform-1 `(if ,condition
                             (progn ,@body)
                           (cond ,@rest))
                        next-state))

    ;; Process `if'.

    (`(if ,cond ,then . ,else)
      (lcr--transform-1 cond
                        (lambda (c)
                          `(if ,c
                               ,(lcr--transform-1 then k)
                             ,(lcr--transform-1 `(progn ,@else) k)))))

    ;; Process `progn' and `inline': they are identical except for the
    ;; name, which has some significance to the byte compiler.

    (`(inline) (lcr--transform-1 nil k))
    (`(inline ,form) (lcr--transform-1 form k))
    (`(inline ,form . ,rest)
     (lcr--transform-1
      form
      (lambda (_) (lcr--transform-1 `(inline ,@rest)
                                    k))))

    (`(progn) (lcr--transform-1 nil k))
    (`(progn ,form) (lcr--transform-1 form k))
    (`(progn ,form . ,rest)
     (lcr--transform-1
      form
      (lambda (_) (lcr--transform-1 `(progn ,@rest)
                                    k))))

    ;; Process `let'.
    (`(let ,bindings . ,body)
     (lcr--transform-n
      (-map #'cadr bindings)
      (lambda (xs) `(let ,(-zip-with 'list (-map #'car bindings) xs)
                      ,(lcr--transform-1 `(progn ,@body) k)))))
    (`(let* () . ,body)
      (lcr--transform-1 `(progn ,@body) k))
    (`(let* ((,var ,value-form) . ,more-bindings) . ,body)
        (lcr--transform-1
         value-form
         (lambda (x) `(let* ((,var ,x)) ,(lcr--transform-1 `(let* ,more-bindings ,@body) k)))))
    ;; Process `or'.
    (`(or) (lcr--transform-1 'nil k))
    (`(or ,condition) (lcr--transform-1 condition k))
    (`(or ,condition . ,rest)
      (lcr--transform-1 condition
                        (lambda (x)
                          `(if ,x
                              ,(funcall k x)
                            ,(lcr--transform-1
                              `(or ,@rest) k)))))
    ;; Process `prog1'.
    (`(prog1 ,first) (lcr--transform-1 first k))
    (`(prog1 ,first . ,body)
      (lcr--transform-1
       first (lambda (x) (lcr--transform-1 `(progn ,@body) (lambda (_) (funcall k x))))))
    ;; Process `prog2'.
    (`(prog2 ,form1 ,form2 . ,body)
      (lcr--transform-1 `(progn ,form1 (prog1 ,form2 ,@body)) k))
    ;; Process `while'.
    (`(while ,test . ,body)
     (let ((while-fun (cl-gensym "while")))
       ;; [while c body]k --> (flet (loop () [c]λx.(if x ([body]λy. (loop) (k nil))) )
       `(flet ((,while-fun ()
                ,(lcr--transform-1
                  test
                  (lambda (x) `(if ,x ,(lcr--transform-1 `(progn ,@body) (lambda (_) `(,while-fun))) ,(funcall k 'nil))))))
          (,while-fun))))
    ;; Process various kinds of `quote'.
    (`(quote ,arg) (funcall k `(quote ,arg)))
    (`(function ,arg) (funcall k `(function ,arg)))


    ;; Process function calls
    (`(with-current-buffer ,buffer . ,body)
     
     )
    (`(lcr-call . (,fun . ,args))
     (let ((var (cl-gensym "v")))
       (lcr--transform-1 fun (lambda (f)
                               (lcr--transform-n args (lambda (xs)
                                                        `(,fun ,@xs (lambda (,var) ,(funcall k var)))))))))
                                                        
    (`(,fun . ,args )
     (let ((var (cl-gensym "v")))
       (lcr--transform-1 fun (lambda (f)
                               (lcr--transform-n args (lambda (xs)
                                                        `(let ((,var (,fun ,@xs))) ,(funcall k var))))))))
    (`(form)
     (error "Special form %S incorrect or not supported" form))))


(lcr--transform-1 '(lcr-call f x y) (lambda (x) x))
(lcr--transform-1 '(while c a) (lambda (x) x))
(lcr--transform-1 '(quote quote) (lambda (x) x))
(lcr--transform-1 '(f x y) (lambda (x) x))
(lcr--transform-1 ''example (lambda (x) x))
(lcr--transform-1 '(and a b) (lambda (x) x))
(lcr--transform-1 '(progn (if a b c) d) (lambda (x) x))
(lcr--transform-1 '(progn a b c d) (lambda (x) x))
(lcr--transform-1 '(if a b c d) (lambda (x) x))
(lcr--transform-1 '(if a (and e f) c d) (lambda (x) x))
(lcr--transform-1 '(let () aowfutn) (lambda (x) x))
(lcr--transform-1 '(let ((x yop)) (and a b)) (lambda (x) x))
(lcr--transform-1 '(let* ((x yop)) (and a b)) (lambda (x) x))
(lcr--transform-1 '(or) (lambda (x) x))
(lcr--transform-1 '(or a) (lambda (x) x))
(lcr--transform-1 '(or a b) (lambda (x) x))
(lcr--transform-1 '(prog1 a b c) (lambda (x) x))
(lcr--transform-1 '(prog2 a b c) (lambda (x) x))
(lcr--transform-n '(x y z) (lambda (xs) xs))
(lcr--transform-n '() (lambda (xs) xs))

(defun lcr--context ()
  "Make a copy of the resonably restorable context.
This is useful for coming back to such a context after control
comes back."
  (point-marker))

(defmacro lcr--with-context (ctx &rest body)
  "Temporarily switch to CTX (if possible) and run BODY."
  (declare (indent 2))
  `(if (marker-buffer ,ctx)
       (with-current-buffer (marker-buffer ,ctx)
         (save-excursion (goto-char ,ctx)
                         ,@body))
     ,@body))

(defun lcr-process-read (process continue)
  "Asynchronously read from PROCESS and CONTINUE.
The amount of data read is unknown.  This function should most
certainly be called within a loop."
  (when (process-filter process)
    (error "Try to read from process (%s), but filter exists already! (%s)" process (process-filter process)))
  (let ((ctx (lcr--context)))
    (set-process-filter
     process
     (lambda (process string)
       (set-process-filter process nil)
       (lcr--with-context ctx
           (funcall continue string))))))
(put 'lcr-process-read 'lcr? t)

(defun lcr-wait (secs continue)
  "Wait SECS then CONTINUE."
  (let ((ctx (lcr--context)))
    (run-with-timer secs 'nil
                    (lambda () (lcr--with-context ctx (funcall continue ())))
                    ())))
(put 'lcr-wait 'lcr? t)


(provide 'lcr)
;;; lcr.el ends here
