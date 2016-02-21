;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname skyscrapers) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f ())))
;;************************************************************
;;
;;                      CS 135
;;                   Assignment10
;;                  Name:Susu Dong
;;                   ID:20455711
;;
;;
;;*************************************************************
;;
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Data definitions
;;
;; A Cell is a (union Nat[>0] '?)
;;
;; A Grid is a (ne-listof (ne-listof Cell))
;; A ClueSet is a (ne-listof Nat[>0])

(define-struct state (grid left right top bottom))
;; A State is a (make-state Grid ClueSet ClueSet ClueSet ClueSet)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; visibility-number: (listof Cell) -> Nat
;; Compute the visibility number of a list of Cells (loc).
;; The numeric entries should not have any duplicates.
;;
;; Examples:
(check-expect (visibility-number empty) 0)
(check-expect (visibility-number '(4 ? 6 5 ? 9)) 3)

(define (visibility-number loc)
;;Contract: count-it : (listof (union Nat Symbol)) Nat -> Nat
;;Purpose: oompute the visibility number of a list of Cells  
  (local [(define (count-it loc acc)
            (cond [(empty? loc) 0]
                  [(equal? '? (first loc)) (count-it (rest loc) acc)]
                  [(> (first loc) acc) (+ 1 (count-it (rest loc) (first loc)))]
                  [else (count-it (rest loc) acc)]))]
    (count-it loc 0)))

;; Tests:
(check-expect (visibility-number '(1 ? 2 ? 5 6)) 4)
(check-expect (visibility-number '(5 6 ? 1 ? 2)) 2)
(check-expect (visibility-number '(? ? 4 ? ? ?)) 1)
(check-expect (visibility-number '(2 1 ? 3 ? 6)) 3)
(check-expect (visibility-number '(8 ? 6 ? 5 ? ? 1)) 1)
(check-expect (visibility-number '(4 ? 1 2)) 1)
(check-expect (visibility-number '(1 2 3)) 3)
(check-expect (visibility-number '(6 5 4 3 2 1)) 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; feasible-visibility? : (listof Cell) Nat -> Boolean
;; Given a partially filled in row lov and a natural number vis 
;; that counts the number of towers that are supposed to be
;; visible, is it possible to fill in the blanks in lov so that
;; the desired visibility number is attained?  Assume that the
;; numeric entries in lov are in a contiguous block at the start
;; or end of the list.

;; Examples:
(check-expect (feasible-visibility? '(3 ? ? ?) 2) true)
(check-expect (feasible-visibility? '(2 1 ? ?) 4) false)

(define (feasible-visibility? lov vis)
  (local [(define in-lo-missing (filter (lambda (x) (not (member? x lov))) (build-list (length lov) add1))) 
          (define de-lo-missing (reverse in-lo-missing))
;;Contract: combine : (listof (union Nat Symbol)) (listof Nat) -> (listof Nat)
;;Purpose: fill the missing numeric entries in the list of cells        
          (define (combine lov lo-missing)
            (cond [(empty? lov) empty]
                  [(empty? lo-missing) lov]
                  [(number? (first lov))
                   (cons (first lov) (combine (rest lov) lo-missing))]
                  [else (cons (first lo-missing) (combine (rest lov) (rest lo-missing)))]))]
    (cond [(and (<= (visibility-number (combine lov de-lo-missing)) vis)
                (>= (visibility-number (combine lov in-lo-missing)) vis)) true]
          [else false])))

;; Tests
(check-expect (feasible-visibility? '(2 ?) 2) false)
(check-expect (feasible-visibility? '(1 3 ?) 2) true)
(check-expect (feasible-visibility? '(3 4 ? ?) 3) false)
(check-expect (feasible-visibility? '(2 3 ? ? ?) 4) true)
(check-expect (feasible-visibility? '(5 ? ? 6 ? ?) 3) false)
(check-expect (feasible-visibility? '(7 ? ? 5 ? ? 1) 1) true)
(check-expect (feasible-visibility? '(? ? 8 ? ? ? ? ?) 4) false)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; valid-state? : State -> Boolean
;; Determine whether the passed-in State a-state can still be legally
;; continued to produce a solution for the entire puzzle.  Rule out
;; any State in which there are duplicate entries in one row or column
;; and any State in which a row or column violates its visibility
;; constraints.

;; Examples:
(check-expect 
 (valid-state? 
  (make-state '((? ? 3) (? ? ?) (? ? ?)) 
              '(1 2 1) '(2 1 1) '(1 1 1) '(2 2 2))) false)
(check-expect
 (valid-state?
  (make-state '((? ? 3) (? ? ?) (? ? ?))
              '(3 1 1) '(1 2 2) '(1 1 1) '(2 2 2))) true) 

(define (valid-state? a-state)
  (local [(define l-to-r-lov-with-vis (map list (state-grid a-state) (state-left a-state)))
          (define r-to-l-lov-with-vis (map list (map reverse (state-grid a-state)) (state-right a-state)))
          (define t-to-b-lov-with-vis (map list (apply map list (state-grid a-state)) (state-top a-state)))
          (define b-to-t-lov-with-vis (map list (map reverse (apply map list (state-grid a-state))) (state-bottom a-state)))
          (define l-to-r-lov (state-grid a-state))
          (define t-to-b-lov (apply map list (state-grid a-state)))
;;Contract: check-duplicate : (listof Nat) -> Boolean
;;Purpose: check if there exists duplicate of numbers in the given list. Produce
;;         false if there exists any duplicate of numbers. Otherwise, produce true.          
          (define (check-duplicate lon)
            (cond [(empty? lon) true]
                  [(member? (first lon) (rest lon)) false]
                  [else (check-duplicate (rest lon))]))]
    (and (andmap (lambda (x) (apply feasible-visibility? x)) l-to-r-lov-with-vis)
         (andmap (lambda (x) (apply feasible-visibility? x)) r-to-l-lov-with-vis)
         (andmap (lambda (x) (apply feasible-visibility? x)) t-to-b-lov-with-vis)
         (andmap (lambda (x) (apply feasible-visibility? x)) b-to-t-lov-with-vis) 
         (andmap check-duplicate (map (lambda (x) (filter number? x)) l-to-r-lov))
         (andmap check-duplicate (map (lambda (x) (filter number? x)) t-to-b-lov)))))


;; Tests:
(check-expect
 (valid-state?
  (make-state '((1 ?) (? ?))
              '(2 1) '(1 2) '(2 1) '(1 2))) true) 
(check-expect
 (valid-state?
  (make-state '((? ? ?) (? 3 ?) (? ? ?))
              '(2 3 1) '(1 2 3) '(2 2 1) '(1 2 3))) false) 
(check-expect
 (valid-state?
  (make-state '((? 4 ? ?) (? ? ? ?) (? ? 3 ?) (? ? ? ?))
              '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))) true) 
(check-expect
 (valid-state?
  (make-state '((? ? ? ? 5) (? ? ? ? ?) (? ? ? ? ?) (? ? ? ? ?) (? ? ? ? ?))
              '(5 4 3 2 1) '(1 2 2 2 2) '(5 4 3 2 2) '(1 2 2 2 2))) false) 
(check-expect
 (valid-state?
  (make-state '((? 2 3 ? ? ?) (2 ? ? ? ? ?) (? ? ? 6 ? ?) (? ? ? 1 ? ?) (? ? ? ? ? 4) (? ? ? ? ? 5))
              '(6 5 4 3 2 1) '(1 2 2 2 2 2) '(6 5 4 3 2 2) '(1 2 2 2 2 2))) true) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; complete-state? : State -> Boolean
;; Determine whether the passed-in State a-state represents a solved
;; puzzle, i.e., one in which the grid has no unknowns left it in
;; (we assume that the puzzle is legal if this is the case).

;; Examples:
(check-expect
 (complete-state?
  (make-state '((? 1 2) (3 2 1) (1 2 3))
              '(1 1 1) '(1 1 1) '(1 1 1) '(1 1 1))) false) 
(check-expect
 (complete-state?
  (make-state '((1 2) (2 1))
              '(2 1) '(1 2) '(2 1) '(1 2))) true)

(define (complete-state? a-state)
  (andmap (lambda (x) (not (member? '? x))) (state-grid a-state)))

;; Tests:
(check-expect
 (complete-state?
  (make-state '((2 1 3) (1 3 2) (3 2 1))
              '(2 2 1) '(1 2 3) '(2 2 1) '(1 2 3))) true) 
(check-expect
 (complete-state?
  (make-state '((1 4 2 3) (4 ? 1 2) (2 1 3 4) (3 ? ? 1))
              '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))) false) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; neighbours : State -> (listof State)
;; Given a current State a-state, produce a list of all legal successor
;; states, according to the constraints laid out in the assignment (that
;; is, fill in the first non-numeric entry in the grid with each of the
;; legal numbers that can live in that spot.

;; Examples:
(check-expect
 (neighbours
  (make-state '((?)) '(1) '(1) '(1) '(1)))
 (list (make-state '((1)) '(1) '(1) '(1) '(1))))
(check-expect
 (neighbours
  (make-state
   (make-list 4 (make-list 4 '?))
   '(1 3 2 2) '(3 2 2 1) '(1 3 2 3) '(2 2 3 1))) 
 (list (make-state '((4 ? ? ?) (? ? ? ?) (? ? ? ?) (? ? ? ?))
                   '(1 3 2 2) '(3 2 2 1) '(1 3 2 3) '(2 2 3 1))))

(define (neighbours a-state)
;;Contract: first-empty-location : Grid Nat -> (listof Nat)
;;Purpose: find the location of the first empty cell and produce a list of 
;;         two numbers. The first number in the list refers to the row where 
;;         the first empty cell exists and the second number refers to the column
;;         where the first empty cell exists.
  (local [(define (first-empty-location grid row)
            (cond [(member? '? (first grid)) 
                   (list row (local [(define (find-column lov)
                                       (cond [(equal? '? (first lov)) 1]
                                             [else (+ 1 (find-column (rest lov)))]))]
                               (find-column (first grid))))]
                  [else (first-empty-location (rest grid) (add1 row))]))
;;Contract: new-grid : Grid (listof Nat) Nat Nat -> Grid
;;Purpose: produce a new grid with the numeric entry filled in the first empty cell of the original grid          
          (define (new-grid grid empty-location n row)
            (cond [(= row (first empty-location)) 
                   (cons (local [(define (replace-n lov column)
                                   (cond [(= column (second empty-location)) (cons n (rest lov))]
                                         [else (cons (first lov) (replace-n (rest lov) (add1 column)))]))]
                           (replace-n (first grid) 1)) (rest grid))]
                  [else (cons (first grid) (new-grid (rest grid) empty-location n (add1 row)))]))
;;Contract: new-state : Grid Nat
;;Purpose: produce a new state with the numeric entry filled in the first empty cell of the original state's grid
          (define (new-state a-state nat-candidate) 
            (make-state (new-grid (state-grid a-state) (first-empty-location (state-grid a-state) 1) nat-candidate 1)
                        (state-left a-state) (state-right a-state)
                        (state-top a-state) (state-bottom a-state)))]
    (filter valid-state? (map (lambda (x y) (new-state x y))
                              (make-list (length (state-grid a-state)) a-state)  
                              (build-list (length (state-grid a-state)) add1)))))
          
;; Tests:
(check-expect
 (neighbours
  (make-state
   (make-list 4 (make-list 4 '?))
   '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))) 
 (list (make-state '((1 ? ? ?) (? ? ? ?) (? ? ? ?) (? ? ? ?))
                   '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))
       (make-state '((2 ? ? ?) (? ? ? ?) (? ? ? ?) (? ? ? ?))
                   '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))
       (make-state '((3 ? ? ?) (? ? ? ?) (? ? ? ?) (? ? ? ?))
                   '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))))

(check-expect
 (neighbours
  (make-state
   '((1 ? ? ?) (? ? ? ?) (? ? ? ?) (? ? ? ?))
   '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))) 
 (list (make-state '((1 4 ? ?) (? ? ? ?) (? ? ? ?) (? ? ? ?))
                   '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))))

(check-expect
 (neighbours
  (make-state
   '((1 4 ? ?) (? ? ? ?) (? ? ? ?) (? ? ? ?))
   '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))) 
 (list (make-state '((1 4 2 ?) (? ? ? ?) (? ? ? ?) (? ? ? ?))
                   '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))))
(check-expect
 (neighbours
  (make-state
   '((1 4 2 ?) (? ? ? ?) (? ? ? ?) (? ? ? ?))
   '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))) 
 (list (make-state '((1 4 2 3) (? ? ? ?) (? ? ? ?) (? ? ? ?))
                   '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))))
(check-expect
 (neighbours
  (make-state
   '((1 4 2 3) (? ? ? ?) (? ? ? ?) (? ? ? ?))
   '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))) 
 (list (make-state '((1 4 2 3) (4 ? ? ?) (? ? ? ?) (? ? ? ?))
                   '(2 1 3 2) '(2 3 1 2) '(2 1 3 2) '(2 3 1 2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; search: (X -> Boolean) (X -> (listof X)) X -> (union X false)
;; Solve a puzzle, given a current State.  Use depth-first search
;; with backtracking, assuming that the search space is acyclic. 
;; The parameters are:
;;  * at-end? -- a predicate that determines whether the given
;;      state is an end state of the search (i.e., a solution).
;;  * neighbours -- a function that maps a current state to a list
;;      of neighbouring states.
;;  * a-state -- the initial state.
;;
;; DO NOT MODIFY THIS FUNCTION.

(define (search at-end? neighbours a-state)
  (local
    [;; find-route: X -> (union X false)
     ;; Search outward from this configuration to see if there's a path
     ;; to a solution.
     (define (find-route a-state)
       (cond
         [(at-end? a-state) a-state]
         [else (find-route/list (neighbours a-state))]))
     
     ;; find-route/list: (listof X) -> (union X false)
     ;; Search outward from every configuration in the passed-in list of
     ;; configurations.  If any one of them leads to a solution, stop and
     ;; produce that solution.  Produce false if you run out of options.
     (define (find-route/list lostate)
       (cond
         [(empty? lostate) false]
         [else
          (local
            [(define cur (find-route (first lostate)))]
            (cond
              [(not (boolean? cur)) cur]
              [else (find-route/list (rest lostate))]))]))]
    (find-route a-state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Sample puzzles for testing.  You can easily create more yourself by 
;; transcribing them from examples generated using the software mentioned
;; in the assignment.
;;

;; The puzzle that appears at the start of the assignment handout.
(define assignment-puzzle
  (make-state
   (make-list 4 (make-list 4 '?))
   '(1 3 2 2)
   '(3 2 2 1)
   '(1 3 2 3)
   '(2 2 3 1)))
(define assignment-puzzle-solution
  (make-state
   '((4 1 3 2) (2 3 4 1) (1 4 2 3) (3 2 1 4))
   (state-left assignment-puzzle)
   (state-right assignment-puzzle)
   (state-top assignment-puzzle)
   (state-bottom assignment-puzzle)))

(define puzzle-1 
  (make-state
   (make-list 4 (make-list 4 '?))
   '(1 2 2 3)
   '(3 3 1 2)
   '(1 2 3 2)
   '(3 2 1 2)))
(define puzzle-1-solution 
  (make-state
   '((4 3 1 2) (2 4 3 1) (3 1 2 4) (1 2 4 3))
   (state-left puzzle-1)
   (state-right puzzle-1)
   (state-top puzzle-1)
   (state-bottom puzzle-1)))

(define puzzle-2 
  (make-state
   (make-list 4 (make-list 4 '?))
   '(1 2 3 2)
   '(3 3 2 1)
   '(1 2 3 3)
   '(2 3 2 1)))
(define puzzle-2-solution 
  (make-state
   '((4 3 1 2) 
     (2 4 3 1) 
     (1 2 4 3) 
     (3 1 2 4))
   (state-left puzzle-2)
   (state-right puzzle-2)
   (state-top puzzle-2)
   (state-bottom puzzle-2)))

(define puzzle-3 
  (make-state
   (make-list 5 (make-list 5 '?))
   '(2 3 2 1 3)
   '(2 1 2 3 2)
   '(4 1 2 3 2) 
   '(2 5 2 1 2)))
(define puzzle-3-solution 
  (make-state
   '((1 5 2 3 4) 
     (3 4 1 2 5)
     (4 3 5 1 2)
     (5 2 3 4 1)
     (2 1 4 5 3))
   (state-left puzzle-3)
   (state-right puzzle-3)
   (state-top puzzle-3)
   (state-bottom puzzle-3)))

(define puzzle-4 
  (make-state
   (make-list 5 (make-list 5 '?))
   '(2 2 1 2 4)
   '(3 2 5 3 1)
   '(3 1 3 2 3) 
   '(3 3 2 3 1)))
(define puzzle-4-solution 
  (make-state
   '((1 5 2 4 3) 
     (3 2 1 5 4)
     (5 4 3 2 1)
     (4 1 5 3 2)
     (2 3 4 1 5))
   (state-left puzzle-4)
   (state-right puzzle-4)
   (state-top puzzle-4)
   (state-bottom puzzle-4)))

(define bonus-puzzle
  (make-state
   '((? ? ? ? ? ?)
     (? ? ? ? ? ?)
     (? ? ? ? ? ?)
     (? ? ? ? ? ?)
     (? ? ? ? ? ?)
     (? ? ? 2 ? ?))
   '(2 4 ? ? ? ?)
   '(4 ? 4 ? 2 2)
   '(? 2 ? ? ? 4)
   '(? ? ? ? 4 ?)))

;; Testing example:
(check-expect (search complete-state? neighbours puzzle-4) puzzle-4-solution)
