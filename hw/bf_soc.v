// bf_soc -- bf_chip plus block-RAM program and tape memories.
// This is the module to put on an FPGA: connect clk, an active-high reset,
// the two UART pins, and optionally an LED to `halted`.

module bf_soc #(
    parameter XLEN         = 64,            // cell / register width
    parameter CLKS_PER_BIT = 104,           // clk Hz / baud
    parameter RX_FIFO_AW   = 4,             // 16-byte input buffer
    parameter IMEM_AW      = 12,
    parameter DMEM_AW      = 12,
    parameter PSTACK_AW    = 6,
    parameter RSTACK_AW    = 6,
    parameter IMEM_INIT    = "program.hex"
) (
    input  wire clk,
    input  wire rst,
    input  wire uart_rx,
    output wire uart_tx,
    output wire halted
);
    wire [IMEM_AW-1:0] imem_addr;
    wire [DMEM_AW-1:0] dmem_addr;
    wire               dmem_we;
    wire [XLEN-1:0]    dmem_wdata;
    reg  [7:0]         imem_q;
    reg  [XLEN-1:0]    dmem_q;

    bf_chip #(
        .XLEN(XLEN), .CLKS_PER_BIT(CLKS_PER_BIT), .RX_FIFO_AW(RX_FIFO_AW),
        .IMEM_AW(IMEM_AW), .DMEM_AW(DMEM_AW),
        .PSTACK_AW(PSTACK_AW), .RSTACK_AW(RSTACK_AW)
    ) chip (
        .clk(clk), .rst(rst),
        .uart_rx(uart_rx), .uart_tx(uart_tx), .halted(halted),
        .imem_addr(imem_addr), .imem_rdata(imem_q),
        .dmem_addr(dmem_addr), .dmem_rdata(dmem_q),
        .dmem_we(dmem_we), .dmem_wdata(dmem_wdata)
    );

    reg [7:0]      imem [0:(1<<IMEM_AW)-1];
    reg [XLEN-1:0] dmem [0:(1<<DMEM_AW)-1];

    integer i;
    initial begin
        for (i = 0; i < (1<<IMEM_AW); i = i + 1) imem[i] = 8'h60;  // HALT
        for (i = 0; i < (1<<DMEM_AW); i = i + 1) dmem[i] = {XLEN{1'b0}};
        $readmemh(IMEM_INIT, imem);
    end

    always @(posedge clk) begin
        imem_q <= imem[imem_addr];
        if (dmem_we) dmem[dmem_addr] <= dmem_wdata;
        dmem_q <= dmem[dmem_addr];
    end
endmodule
