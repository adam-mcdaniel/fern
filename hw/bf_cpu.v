// bf_cpu -- multi-cycle core for the brainfuck extension in src/lib.rs.
//
// Harvard machine: byte-wide program memory, XLEN-bit word-addressed tape.
// Both memories live outside the core (block RAM in bf_soc, external SRAM
// chips around bf_chip) and must be synchronous: read data for an address
// arrives one cycle later, and writes happen at the clock edge.
// Registers:  A  accumulator          P  tape pointer (cell index)
//             PC program counter      O  operand register (built by prefixes)
// plus two on-chip stacks: one for `*`/`&` (saved P) and one for `!`/`;`.
//
// Every instruction takes two cycles: FETCH latches the instruction byte,
// M[P] and the top of both stacks; EXEC executes it.  READ/WRITE stay in
// EXEC until the stream handshake completes.  The ISA is documented in hw/README.md.

module bf_cpu #(
    parameter XLEN      = 64,           // width of A, P, O and tape cells (>= 8)
    parameter IMEM_AW   = 12,           // 2^IMEM_AW bytes of program
    parameter DMEM_AW   = 12,           // 2^DMEM_AW tape cells
    parameter PSTACK_AW = 6,            // `*`/`&` stack depth (2^N, wraps)
    parameter RSTACK_AW = 6             // call stack depth (2^N, wraps)
) (
    input  wire       clk,
    input  wire       rst,

    // program memory
    output wire [IMEM_AW-1:0] imem_addr,
    input  wire [7:0]         imem_rdata,

    // tape memory
    output wire [DMEM_AW-1:0] dmem_addr,
    input  wire [XLEN-1:0]    dmem_rdata,
    output reg                dmem_we,
    output reg  [XLEN-1:0]    dmem_wdata,

    // stdin byte stream (`,`)
    input  wire [7:0] in_data,
    input  wire       in_valid,
    output wire       in_ready,

    // stdout byte stream (`.`)
    output wire [7:0] out_data,
    output wire       out_valid,
    input  wire       out_ready,

    output reg        halted
);
    localparam PFX = 4'h0, NFX = 4'h1, LIT = 4'h2, MOV = 4'h3,
               JZ  = 4'h4, JNZ = 4'h5, OPR = 4'h6;

    localparam HALT = 4'd0,  LOAD  = 4'd1,  STORE = 4'd2,  ADD   = 4'd3,
               NEG  = 4'd4,  POS   = 4'd5,  WHERE = 4'd6,  DEREF = 4'd7,
               REFER = 4'd8, CALL  = 4'd9,  RET   = 4'd10, READ  = 4'd11,
               WRITE = 4'd12;

    localparam S_FETCH = 1'b0, S_EXEC = 1'b1;

    // Code and tape addresses travel through A and P, so they must fit.
    generate
        if (XLEN < 8)        initial $fatal(1, "bf_cpu: XLEN must be at least 8");
        if (IMEM_AW > XLEN)  initial $fatal(1, "bf_cpu: IMEM_AW must be <= XLEN");
        if (DMEM_AW > XLEN)  initial $fatal(1, "bf_cpu: DMEM_AW must be <= XLEN");
    endgenerate

    reg [IMEM_AW-1:0] pc;
    reg [XLEN-1:0]    a, p, o;
    reg               state;

    // ---- memories -------------------------------------------------------
    // The memories are read every cycle at PC and P.  P and PC only change
    // at the end of EXEC, so by the next EXEC both reads reflect the new
    // values and any store made by the previous instruction.
    assign imem_addr = pc;
    assign dmem_addr = p[DMEM_AW-1:0];
    wire [7:0]      ir = imem_rdata;    // instruction byte at pc
    wire [XLEN-1:0] mq = dmem_rdata;    // M[P]

    // Stacks follow the same pattern: pushes write at the end of EXEC and
    // the entry below the stack pointer is latched every cycle, so ptop/rtop
    // are the top of each stack by the next EXEC.
    reg [XLEN-1:0]      pstack [0:(1<<PSTACK_AW)-1];
    reg [IMEM_AW-1:0]   rstack [0:(1<<RSTACK_AW)-1];
    reg [PSTACK_AW-1:0] psp;
    reg [RSTACK_AW-1:0] rsp;
    reg [XLEN-1:0]      ptop;
    reg [IMEM_AW-1:0]   rtop;
    wire                p_push, r_push;
    wire [IMEM_AW-1:0]  pc_next = pc + 1'b1;

    always @(posedge clk) begin
        if (p_push) pstack[psp] <= p;
        ptop <= pstack[psp - 1'b1];
    end

    always @(posedge clk) begin
        if (r_push) rstack[rsp] <= pc_next;
        rtop <= rstack[rsp - 1'b1];
    end

    // ---- decode ---------------------------------------------------------
    wire [3:0]  opcode  = ir[7:4];
    // Narrower values are zero-extended to XLEN throughout.
    wire [XLEN-1:0] operand = o | ir[3:0];
    wire        is_opr  = state == S_EXEC && opcode == OPR && !halted && !rst;

    assign in_ready  = is_opr && operand == READ;
    assign out_valid = is_opr && operand == WRITE;
    assign out_data  = a[7:0];

    wire stall = (in_ready && !in_valid) || (out_valid && !out_ready);

    assign p_push = is_opr && operand == DEREF;
    assign r_push = is_opr && operand == CALL;

    always @* begin
        dmem_we    = is_opr && operand == STORE;
        dmem_wdata = a;
    end

    // ---- execute --------------------------------------------------------
    always @(posedge clk) begin
        if (rst) begin
            pc     <= 0;
            a      <= 0;
            p      <= 0;
            o      <= 0;
            psp    <= 0;
            rsp    <= 0;
            state  <= S_FETCH;
            halted <= 1'b0;
        end else if (!halted) begin
            case (state)
            S_FETCH: state <= S_EXEC;

            S_EXEC: if (!stall) begin
                state <= S_FETCH;
                pc    <= pc_next;
                o     <= 0;
                case (opcode)
                PFX: o <= (o | ir[3:0]) << 4;
                NFX: o <= ~(o | ir[3:0]) << 4;
                LIT: a <= operand;
                MOV: p <= p + operand;
                JZ:  if (a == 0) pc <= pc_next + operand[IMEM_AW-1:0];
                JNZ: if (a != 0) pc <= pc_next + operand[IMEM_AW-1:0];
                OPR: case (operand)
                    LOAD:  a <= mq;
                    ADD:   a <= a + mq;
                    STORE: ;                            // see dmem_we above
                    NEG:   a <= -a;
                    POS:   a <= $signed(a) > 0;
                    WHERE: a <= p;
                    DEREF: begin                        // push: see p_push
                        psp <= psp + 1'b1;
                        p   <= mq;
                    end
                    REFER: begin
                        p   <= ptop;
                        psp <= psp - 1'b1;
                    end
                    CALL: begin                         // push: see r_push
                        rsp <= rsp + 1'b1;
                        pc  <= a[IMEM_AW-1:0];
                    end
                    RET: begin
                        pc  <= rtop;
                        rsp <= rsp - 1'b1;
                    end
                    READ:  a <= in_data;
                    WRITE: ;                            // handshake only
                    default: begin                      // HALT and illegal ops
                        halted <= 1'b1;
                        pc     <= pc;
                    end
                    endcase
                default: begin                          // illegal opcode
                    halted <= 1'b1;
                    pc     <= pc;
                end
                endcase
            end
            endcase
        end
    end
endmodule
