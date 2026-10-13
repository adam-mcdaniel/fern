// 8N1 UART transmitter, receiver, and a small FIFO for buffering input.
// CLKS_PER_BIT = clock frequency / baud rate (e.g. 12 MHz / 115200 = 104).

module uart_tx #(
    parameter CLKS_PER_BIT = 104
) (
    input  wire       clk,
    input  wire       rst,
    input  wire [7:0] data,
    input  wire       valid,
    output wire       ready,
    output wire       tx
);
    reg [9:0] shift;        // {stop, data, start}, shifted out LSB first
    reg [3:0] bits_left;
    reg [$clog2(CLKS_PER_BIT+1)-1:0] cnt;

    assign ready = bits_left == 0;
    assign tx    = shift[0];

    always @(posedge clk) begin
        if (rst) begin
            shift     <= 10'h3ff;
            bits_left <= 0;
            cnt       <= 0;
        end else if (bits_left == 0) begin
            if (valid) begin
                shift     <= {1'b1, data, 1'b0};
                bits_left <= 10;
                cnt       <= 0;
            end
        end else if (cnt == CLKS_PER_BIT - 1) begin
            cnt       <= 0;
            shift     <= {1'b1, shift[9:1]};
            bits_left <= bits_left - 1'b1;
        end else begin
            cnt <= cnt + 1'b1;
        end
    end
endmodule

module uart_rx #(
    parameter CLKS_PER_BIT = 104
) (
    input  wire       clk,
    input  wire       rst,
    input  wire       rx,
    output reg  [7:0] data,
    output reg        valid     // one-cycle pulse per received byte
);
    localparam IDLE = 2'd0, START = 2'd1, DATA = 2'd2, STOP = 2'd3;

    reg       rx_meta, rx_sync;     // two-flop synchronizer
    reg [1:0] state;
    reg [2:0] bit_idx;
    reg [7:0] shift;
    reg [$clog2(CLKS_PER_BIT+1)-1:0] cnt;

    always @(posedge clk) begin
        rx_meta <= rx;
        rx_sync <= rx_meta;
        valid   <= 1'b0;
        if (rst) begin
            rx_meta <= 1'b1;
            rx_sync <= 1'b1;
            state   <= IDLE;
            cnt     <= 0;
        end else case (state)
            IDLE: if (!rx_sync) begin
                state <= START;
                cnt   <= 0;
            end
            START: if (cnt == (CLKS_PER_BIT - 1) / 2) begin
                // Middle of the start bit: still low means it was real.
                state   <= rx_sync ? IDLE : DATA;
                cnt     <= 0;
                bit_idx <= 0;
            end else cnt <= cnt + 1'b1;
            DATA: if (cnt == CLKS_PER_BIT - 1) begin
                cnt     <= 0;
                shift   <= {rx_sync, shift[7:1]};
                bit_idx <= bit_idx + 1'b1;
                if (bit_idx == 3'd7) state <= STOP;
            end else cnt <= cnt + 1'b1;
            STOP: if (cnt == CLKS_PER_BIT - 1) begin
                state <= IDLE;
                if (rx_sync) begin          // drop bytes with a framing error
                    data  <= shift;
                    valid <= 1'b1;
                end
            end else cnt <= cnt + 1'b1;
        endcase
    end
endmodule

// Synchronous FIFO; pushes while full are dropped.
module fifo #(
    parameter W  = 8,
    parameter AW = 4
) (
    input  wire         clk,
    input  wire         rst,
    input  wire [W-1:0] in_data,
    input  wire         in_valid,
    output wire [W-1:0] out_data,
    output wire         out_valid,
    input  wire         out_ready
);
    reg [W-1:0] mem [0:(1<<AW)-1];
    reg [AW:0]  rd, wr;

    wire empty = rd == wr;
    wire full  = rd[AW-1:0] == wr[AW-1:0] && rd[AW] != wr[AW];

    assign out_valid = !empty;
    assign out_data  = mem[rd[AW-1:0]];

    always @(posedge clk) begin
        if (rst) begin
            rd <= 0;
            wr <= 0;
        end else begin
            if (in_valid && !full) begin
                mem[wr[AW-1:0]] <= in_data;
                wr <= wr + 1'b1;
            end
            if (out_valid && out_ready) rd <= rd + 1'b1;
        end
    end
endmodule
