module gold(
  input [32:0] A,
  input [32:0] B,
  output [32:0] O1,
  output [32:0] O2
);
  assign O1 = A - B;
  assign O2 = B - A;
endmodule
