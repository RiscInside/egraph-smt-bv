module optimized(
    input wire [31:0] A, B,
    output wire [32:0] Z
);
assign Z = B + A;
endmodule
