
module improve(
    input wire s1,
    input wire s2,
    input wire a,
    input wire b,
    input wire c,
    input wire d,
    output wire y
);
    wire x0, x1, x2;
    improve_mux2to1 mux0 (.in0(c), .in1(d), .sel(s2), .out(x0));
    improve_mux2to1 mux1 (.in0(s1), .in1(x0), .sel(s2), .out(x1));
    improve_mux2to1 mux2 (.in0(a), .in1(b), .sel(x1), .out(y));
endmodule

// 2-to-1 Multiplexer Module
module improve_mux2to1(
    input wire in0,
    input wire in1,
    input wire sel,
    output reg out
);
    always @(*) begin
        out = sel ? in1 : in0; // Use ternary operator for clarity
    end
endmodule
