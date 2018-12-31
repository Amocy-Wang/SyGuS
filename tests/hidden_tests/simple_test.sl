

(set-logic LIA)

(synth-fun simple_func ((x Int)) Int
    ((Start Int (
                 x
                 1
                 2
                 3
                 (* Start Start)
                 (mod Start Start)))))

(declare-var x Int)

(constraint (= (f x) x))

(check-synth)

