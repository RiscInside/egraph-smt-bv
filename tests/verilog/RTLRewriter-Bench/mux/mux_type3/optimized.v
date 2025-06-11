module optimized(
    input wire sel,
    input wire a,
    output wire y
);
    assign y = a | sel;
endmodule
