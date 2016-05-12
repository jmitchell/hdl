chip(nand, true, true, false).
chip(nand, false, false, true).
chip(nand, false, true, true).
chip(nand, true, false, true).

chip(and, A, B, C) :-
    chip(nand, A, B, X),
    chip(not, X, C).

chip(or, A, B, C) :-
    chip(not, A, X),
    chip(not, B, Y),
    chip(nand, X, Y, C).

chip(xor, A, B, C) :-
    chip(nand, A, B, N),
    chip(or, A, B, O),
    chip(and, N, O, C).

chip(nor, A, B, C) :-
    chip(or, A, B, O),
    chip(not, O, C).

chip(not, I, O) :-
    chip(nand, I, I, O).

chip(half_adder, A, B, S, C) :-
    chip(xor, A, B, S),
    chip(and, A, B, C).

chip(mux, A, _, false, A).
chip(mux, _, B, true, B).

chip(mux2, A, B, C, D, S1, S0, O) :-
    chip(mux, A, B, S1, AB),
    chip(mux, C, D, S1, CD),
    cihp(mux, AB, CD, S0, O).

chip(mux4,
     A1, A2, A3, A4,
     A5, A6, A7, A8,
     A9, A10, A11, A12,
     A13, A14, A15, A16,
     S3, S2, S1, S0, O) :-
    chip(mux2, A1, A2, A3, A4, S3, S2, A_1_4),
    chip(mux2, A5, A6, A7, A8, S3, S2, A_5_8),
    chip(mux2, A9, A10, A11, A12, S3, S2, A_9_12),
    chip(mux2, A13, A14, A15, A16, S3, S2, A_13_16),
    chip(mux2, A_1_4, A_5_8, A_9_12, A_13_16, S1, S0, O).

chip(full_adder, A, B, Cin, S, Cout) :-
    chip(xor, A, B, X),
    chip(xor, X, Cin, S),
    chip(and, A, B, Y),
    chip(and, X, Cin, Z),
    chip(or, Y, Z, Cout).

chip(full_adder2, A1, A0, B1, B0, Cin, S1, S0, Cout) :-
    chip(full_adder, A0, B0, Cin, S0, C1),
    chip(full_adder, A1, B1, C1, S1, Cout).

chip(full_adder4,
     A3, A2, A1, A0,
     B3, B2, B1, B0,
     Cin,
     S3, S2, S1, S0,
     Cout) :-
    chip(full_adder2, A1, A0, B1, B0, Cin, S1, S0, C1),
    chip(full_adder2, A3, A2, B3, B2, C1, S3, S2, Cout).

chip(full_adder8,
     A7, A6, A5, A4, A3, A2, A1, A0,
     B7, B6, B5, B4, B3, B2, B1, B0,
     Cin,
     S7, S6, S5, S4, S3, S2, S1, S0,
     Cout) :-
    chip(full_adder4,
         A3, A2, A1, A0,
         B3, B2, B1, B0,
         Cin,
         S3, S2, S1, S0,
         C1),
    chip(full_adder4,
         A7, A6, A5, A4,
         B7, B6, B5, B4,
         C1,
         S7, S6, S5, S4,
         Cout).
