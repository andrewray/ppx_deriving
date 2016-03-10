open OUnit2

module T : sig

  type a = int option [@@deriving map2,show]

  type b = B of int [@@deriving map2,show]

  type 'a c = C of 'a [@@deriving map2,show]

  type ('a,'b) d = D1 of ('a,'b) d * 'a * ('a,'b) d | D2 of 'b [@@deriving map2,show] 

  type ('a,'b,'c) e = 
    {
      e0 : int;
      e1 : ('a,'b,'c) e option;
      e2 : ('a * 'c) list;
      e3 : 'b array;
    } [@@deriving map2,show]

end = struct

  type a = int option [@@deriving map2,show]

  type b = B of int [@@deriving map2,show]

  type 'a c = C of 'a [@@deriving map2,show]

  type ('a,'b) d = D1 of ('a,'b) d * 'a * ('a,'b) d | D2 of 'b [@@deriving map2,show] 

  type ('a,'b,'c) e = 
    {
      e0 : int;
      e1 : ('a,'b,'c) e option;
      e2 : ('a * 'c) list;
      e3 : 'b array;
    } [@@deriving map2,show]

end

open T

let fmt_chr fmt = Format.fprintf fmt "%c"
let fmt_flt fmt = Format.fprintf fmt "%f"
let fmt_int fmt = Format.fprintf fmt "%d"
let fmt_str fmt = Format.fprintf fmt "%s"

let test_b ctxt = assert_equal ~printer:show_b (B 1) (map2_b (B 1) (B 2))

let test_c ctxt =
  assert_equal ~printer:(show_c fmt_int) (C 3) (map2_c (+) (C 1) (C 2));
  assert_equal ~printer:(show_c fmt_flt) (C 3.) 
    (map2_c (fun a b -> float_of_int (a+b)) (C 2) (C 1))

let test_d ctxt = 
  assert_equal ~printer:(show_d fmt_int fmt_str)
    (D1(D1(D2 "ab", 5, D2 "cd"), 7, D2 "ef"))
    (map2_d (+) (^)
      (D1(D1(D2 "a", 2, D2 "c"), 3, D2 "e"))
      (D1(D1(D2 "b", 3, D2 "d"), 4, D2 "f")));
  assert_equal ~printer:(show_d fmt_int fmt_flt)
    (D1(D1(D2 3., 5, D2 7.), 7, D2 11.))
    (map2_d (fun a b -> int_of_float (a +. b)) (fun a b -> float_of_int (a+b))
      (D1(D1(D2 1, 2., D2 1), 3., D2 5))
      (D1(D1(D2 2, 3., D2 6), 4., D2 6)))

let test_e ctxt = 
  assert_equal ~printer:(show_e fmt_int fmt_str fmt_flt)
    { e0=4; e1=Some({e0=3; e1=None; e2=[]; e3=[||]}); e2=[(3,6.)]; e3=[|"ax";"by"|] }
    (map2_e (+) (^) (+.)
      { e0=4; e1=Some({e0=3; e1=None; e2=[]; e3=[||]}); e2=[(1,2.)]; e3=[|"a";"b"|] }
      { e0=5; e1=Some({e0=4; e1=None; e2=[]; e3=[||]}); e2=[(2,4.)]; e3=[|"x";"y"|] });
  assert_equal ~printer:(show_e fmt_int fmt_str fmt_flt)
    { e0=4; e1=None; e2=[(3,6.)]; e3=[|"ax";"by"|] }
    (map2_e (fun a b -> int_of_float (a +. b)) (^) (fun a b -> float_of_int (a+b))
      { e0=4; e1=None; e2=[(1.,2)]; e3=[|"a";"b"|] }
      { e0=5; e1=None; e2=[(2.,4)]; e3=[|"x";"y"|] })

let suite = "Test deriving(map2)" >::: [
  "test_b" >:: test_b;
  "test_c" >:: test_c;
  "test_d" >:: test_d;
  "test_e" >:: test_e;
]

