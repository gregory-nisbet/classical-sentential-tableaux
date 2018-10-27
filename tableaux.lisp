;; method of analytic tableaux lisp

;; nil is still false so just return the symbol
(defmethod positive-literal-p ((expr symbol))
  expr)

;; a list is not a positive literal
(defmethod positive-literal-p ((expr list))
  nil)

(assert (positive-literal-p 'a))
(assert (not (positive-literal-p nil)))

(defmethod negative-literal-p ((expr symbol))
  nil)

;; ignore extra arguments after first two
(defmethod negative-literal-p ((expr list))
  (and
   expr
   (eq 'not (car expr))
   (positive-literal-p (cadr expr))))

(assert (not (negative-literal-p nil)))
(assert (not (negative-literal-p 'a)))
(assert (negative-literal-p '(not a)))

(defun literal-p (expr)
  (or (positive-literal-p expr) (negative-literal-p expr)))

(defmethod literal-freevar ((expr symbol))
  expr)

(defmethod literal-freevar ((expr list))
  (and
   (negative-literal-p expr)
   (cadr expr)))

(defmethod headed-by ((sym symbol) (expr symbol))
  nil)

(defmethod headed-by ((sym symbol) (expr list))
  (eq (car expr) sym))

;; refutation context
;; A refutation context is a context that contains
;; the conjunction of statements we're interested
;; in proving or disproving
(defstruct (refutation-context (:conc-name nil))
  conjuncts
  pos-vars
  neg-vars)

;; a refutation result is either a proof or a counter
;; example
(defstruct (refutation-result (:conc-name nil))
  proof
  counterexample)

;; In cases where the tableaux splits there are two proof results
;; coming back from each branch.
;; They need to be unified.
(defmethod proof-product ((x refutation-result) (y refutation-result))
  (cond
   ((and (proof x) (proof y))
    (make-refutation-result
     :proof `(* ,(proof x) ,(proof y))))
   ((counterexample x) x)
   ((counterexample y) y)))

;; tests
(assert
 (equalp
  '(* 4 7)
  (proof (proof-product
	  (make-refutation-result :proof 4)
	  (make-refutation-result :proof 7)))))
(assert
 (equalp
  4
  (counterexample (proof-product
		   (make-refutation-result :counterexample 4)
		   (make-refutation-result :proof 7)))))

;; destructively expand all ands.
;; set up to allow method chaining.
;; That's weird but okay.
(defmethod flatten-and ((r refutation-context))
  (let
      ((did-something nil))
    (setf (conjuncts r)
	  (loop for x in (conjuncts r) appending
		(cond
		 ((headed-by 'and x)
		  (progn
		    ;; record that we needed to flatten an and.
		    ;; means that we haven't reached the fixed point yet.
		    (setf did-something t)
		    (cdr x)))
		 (t (list x)))))
    ;; if we flattened something, then recurse
    ;; if we didn't, then stop.
    (cond
     (did-something (flatten-and r))
     (t r))))

(assert
 (equalp
  '(x y z)
  (conjuncts
   (flatten-and (make-refutation-context
		 :conjuncts (list '(and x y z))
		 :pos-vars nil
		 :neg-vars nil)))))


(defmethod hoist-primitive ((r refutation-context))
  (let
      ((new-conjuncts nil)
       (new-pos-vars (pos-vars r))
       (new-neg-vars (neg-vars r)))
    (loop for expr in (conjuncts r) doing
	  (cond
	   ((positive-literal-p expr)
	    (setf new-pos-vars (cons expr new-pos-vars)))
	   ((negative-literal-p expr)
	    (setf new-neg-vars (cons (literal-freevar expr) new-neg-vars)))
	   (t
	    (setf new-conjuncts (cons expr new-conjuncts)))))
    (progn
      (setf (conjuncts r) (nreverse new-conjuncts))
      (setf (pos-vars r) new-pos-vars)
      (setf (neg-vars r) new-neg-vars)
      r)))


(assert
 (equalp
  (make-refutation-context
   :conjuncts nil
   :pos-vars '(b a)
   :neg-vars '(d c))
  (hoist-primitive
   (make-refutation-context
    :conjuncts '(a b (not c) (not d))
    :pos-vars nil
    :neg-vars nil))))


;; if we have at least one conjunct and it's headed by
;; an or, perform the split
(defmethod split-or ((r refutation-context))
  (and
   (conjuncts r)
   (headed-by 'or (car (conjuncts r)))
   (loop for x in (cdr (car (conjuncts r)))
	 collecting
	 (let
	     ((new-context (copy-structure r)))
	   (setf (conjuncts new-context)
		 (cons
		  x
		  (cdr (conjuncts r))))
	   new-context))))

(assert
 (equalp
  (list
   (make-refutation-context
    :conjuncts '(a)
    :pos-vars nil
    :neg-vars nil)
   (make-refutation-context
    :conjuncts '(b)
    :pos-vars nil
    :neg-vars nil))
  (split-or
   (make-refutation-context
    :conjuncts '((or a b))
    :pos-vars nil
    :neg-vars nil))))


;; take a refutation context ...
;; produce a proof object if there are contradictory literals
;; produce a counterexample object if there are no contradictory literals
;;    and no possibility of producing a contradictory literal
;; produce nil if neither condition is met.
(defmethod refute-once ((r refutation-context))
  (cond
   ;; this test is inefficient. we only need the first item.
   ((intersection (pos-vars r) (neg-vars r))
    ;; TODO: some way of emphasizing the overlap
    ;; also deduplicate and sort.
    (make-refutation-result :proof `(false ,(neg-vars r) -- true ,(pos-vars r))))
   ;; if there is no intersection and the list of conjuncts is
   ;; empty, then we're out of options
   ((not (conjuncts r))
    (make-refutation-result :counterexample `(false ,(neg-vars r) -- true ,(pos-vars r))))
   (t nil)))

(assert
 (proof (refute-once (make-refutation-context
		     :conjuncts nil
		     :pos-vars '(a b)
		     :neg-vars '(b c)))))

(assert
 (counterexample (refute-once (make-refutation-context
			       :conjuncts nil
			       :pos-vars '(a b)
			       :neg-vars '(c d)))))


;; if this shows up somewhere, it's probably a mistake
(defmethod variadic-proof-product ((l null))
  nil)

;; specialize for non-empty list
(defmethod variadic-proof-product ((l cons))
  (reduce #'proof-product l))


(defmethod refute-always ((r refutation-context))
  (let
      ((r1 (hoist-primitive (flatten-and (copy-structure r)))))
    (or
     (refute-once r1)
     ;; This is bad, proof-product should be variadic
     ;; Also this wastes a ton of memory
     (variadic-proof-product (loop for x in (split-or r1)
	     collecting (refute-always x)))
     (t (assert nil)))))


(assert
 (refute-always (make-refutation-context
		 :conjuncts '(and a (not a))
		 :pos-vars nil
		 :neg-vars nil)))


(defun prepend-not ((x list))
  (list 'not x))


(defmethod expand-defns ((expr symbol))
  expr)

(defmethod expand-defns ((expr list))
  (cond
   ;; assume not is unary. don't bother checking it's cool.
   ((headed-by 'not expr)
    (expand-defns-negated (cadr expr)))
   ((headed-by 'and expr)
    `(and ,@(mapcar #'expand-defns (cdr expr))))
   ((headed-by 'or expr)
    `(or ,@(mapcar #'expand-defns (cdr expr))))
   ;; in implication only the first element is a condition
   ;; the rest are alternatives.
   ;; it's like the opposite of a horn clause but whatever.
   ((headed-by 'imp expr)
    (expand-defns `(or (not ,(cadr expr)) ,@(cddr expr))))
   ;; iff is also variadic.
   ;; either everything is true or everything is false.
   ((headed-by 'iff expr)
    (expand-defns `(or (and ,@(cdr expr))
		       (and ,@(mapcar #'prepend-not (cdr expr))))))))

(defmethod expand-defns-negated ((expr symbol))
  `(not ,expr))

(defmethod expand-defns-negated ((expr list))
  (cond
   ((headed-by 'not expr)
    (expand-defns (cadr expr)))
   ((headed-by 'and expr)
    (expand-defns `(or ,@(mapcar #'prepend-not (cdr expr)))))
   ((headed-by 'or expr)
    (expand-defns `(and ,@(mapcar #'prepend-not (cdr expr)))))
   ;; this is really inefficient but who cares
   ((headed-by 'imp expr)
    (expand-defns `(not ,(expand-defns expr))))
   ;; ditto
   ((headed-by 'iff expr)
    (expand-defns `(not ,(expand-defns expr))))))


(assert
 (equalp
  'a
  (expand-defns 'a)))
(assert
 (equalp
  '(not a)
  (expand-defns '(not a))))
(assert
 (equalp
  '(or (not a) (not b))
  (expand-defns '(or (not a) (not b)))))
(assert
 (equalp
  '(and (not a) (not b))
  (expand-defns '(not (or a b)))))
(assert
 (equalp
  '(or (not a) b)
  (expand-defns '(imp a b))))
(assert
 (equalp
  '(or (and a b) (and (not a) (not b)))
  (expand-defns '(iff a b))))
(assert
 (equalp
  '(and a (not b))
  (expand-defns '(not (imp a b)))))
(assert
 (equalp
  '(and (or (not a) (not b)) (or a b))
  (expand-defns '(not (iff a b)))))


(defun prove-one (expr)
  (refute-always
   (make-refutation-context
    :conjuncts (list (expand-defns-negated expr))
    :pos-vars nil
    :neg-vars nil)))

(defun prove (&rest exprs)
  (prove-one (cons 'and exprs)))

(assert (proof (prove '(imp a a))))
(assert (counterexample (prove 'a)))
(assert (proof (prove '(iff a a))))
(assert (proof (prove '(imp (and (iff a b) (iff b c)) (iff a c)))))
(assert (counterexample (prove 'a 'b)))

