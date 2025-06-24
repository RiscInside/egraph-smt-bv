module gate(
  input [32:0] A,
  input [32:0] B,
  output [32:0] O1,
  output [32:0] O2
);
  assign O1 = ~(B + ~A);
  assign O2 = (B + ~A) + 1;
endmodule
