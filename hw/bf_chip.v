// bf_chip -- bf_cpu wired to a UART: `,` reads from RX, `.` writes to TX.
// The program and tape memories are outside: synchronous SRAMs (read data
// arrives one clock after the address; writes happen at the clock edge).
// This is the top level for an ASIC; bf_soc adds block-RAM memories for an
// FPGA.

module bf_chip #(
    parameter XLEN         = 64,            // cell / register width
    parameter CLKS_PER_BIT = 104,           // clk Hz / baud
    parameter RX_FIFO_AW   = 4,             // 16-byte input buffer
    parameter IMEM_AW      = 12,
    parameter DMEM_AW      = 12,
    parameter PSTACK_AW    = 6,
    parameter RSTACK_AW    = 6
) (
    input  wire               clk,
    input  wire               rst,
    input  wire               uart_rx,
    output wire               uart_tx,
    output wire               halted,

    // program memory
    output wire [IMEM_AW-1:0] imem_addr,
    input  wire [7:0]         imem_rdata,

    // tape memory
    output wire [DMEM_AW-1:0] dmem_addr,
    input  wire [XLEN-1:0]    dmem_rdata,
    output wire               dmem_we,
    output wire [XLEN-1:0]    dmem_wdata
);
    wire [7:0] rx_byte;
    wire       rx_valid;
    wire [7:0] in_data;
    wire       in_valid, in_ready;
    wire [7:0] out_data;
    wire       out_valid, out_ready;

    uart_rx #(.CLKS_PER_BIT(CLKS_PER_BIT)) rx (
        .clk(clk), .rst(rst), .rx(uart_rx),
        .data(rx_byte), .valid(rx_valid)
    );

    fifo #(.W(8), .AW(RX_FIFO_AW)) rx_fifo (
        .clk(clk), .rst(rst),
        .in_data(rx_byte), .in_valid(rx_valid),
        .out_data(in_data), .out_valid(in_valid), .out_ready(in_ready)
    );

    uart_tx #(.CLKS_PER_BIT(CLKS_PER_BIT)) tx (
        .clk(clk), .rst(rst),
        .data(out_data), .valid(out_valid), .ready(out_ready),
        .tx(uart_tx)
    );

    bf_cpu #(
        .XLEN(XLEN),
        .IMEM_AW(IMEM_AW), .DMEM_AW(DMEM_AW),
        .PSTACK_AW(PSTACK_AW), .RSTACK_AW(RSTACK_AW)
    ) cpu (
        .clk(clk), .rst(rst),
        .imem_addr(imem_addr), .imem_rdata(imem_rdata),
        .dmem_addr(dmem_addr), .dmem_rdata(dmem_rdata),
        .dmem_we(dmem_we), .dmem_wdata(dmem_wdata),
        .in_data(in_data), .in_valid(in_valid), .in_ready(in_ready),
        .out_data(out_data), .out_valid(out_valid), .out_ready(out_ready),
        .halted(halted)
    );
endmodule
