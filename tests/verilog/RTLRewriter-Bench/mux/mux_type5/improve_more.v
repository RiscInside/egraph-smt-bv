module improve_more(
    input wire s1,
    input wire s2,
    input wire a,
    input wire b,
    input wire d,
    output wire y
);
    wire x0;
    improve_more_mux2to1 mux0 (.in0(s1), .in1(d), .sel(s2), .out(x0));
    improve_more_mux2to1 mux2 (.in0(a), .in1(b), .sel(x0), .out(y));
endmodule

// 2-to-1 Multiplexer Module
module improve_more_mux2to1(
    input wire in0,
    input wire in1,
    input wire sel,
    output reg out
);
    always @(*) begin
        out = sel ? in1 : in0; // Use ternary operator for clarity
    end
endmodule
