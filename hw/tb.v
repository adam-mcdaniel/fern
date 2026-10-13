// Simulation testbench: feeds a file into the UART RX pin, decodes the TX
// pin to stdout, and finishes once the CPU halts and TX is idle.
//
//   +in=<file>         bytes to send as stdin (optional)
//   +max_cycles=<n>    give up after n cycles (default 50M)

`timescale 1ns/1ps

module tb;
    parameter PROG         = "program.hex";
    parameter CLKS_PER_BIT = 8;
    parameter IMEM_AW      = 12;
    parameter DMEM_AW      = 12;
    parameter XLEN         = 64;

    reg  clk = 0;
    reg  rst = 1;
    reg  rx  = 1;
    wire tx;
    wire halted;

    always #5 clk = ~clk;

    bf_soc #(
        .CLKS_PER_BIT(CLKS_PER_BIT),
        .RX_FIFO_AW(10),
        .IMEM_AW(IMEM_AW),
        .DMEM_AW(DMEM_AW),
        .XLEN(XLEN),
        .IMEM_INIT(PROG)
    ) dut (
        .clk(clk), .rst(rst), .uart_rx(rx), .uart_tx(tx), .halted(halted)
    );

    task send_byte(input [7:0] b);
        integer k;
        begin
            rx = 0;
            repeat (CLKS_PER_BIT) @(posedge clk);
            for (k = 0; k < 8; k = k + 1) begin
                rx = b[k];
                repeat (CLKS_PER_BIT) @(posedge clk);
            end
            rx = 1;
            repeat (CLKS_PER_BIT) @(posedge clk);
        end
    endtask

    // stdin
    reg [8*1024-1:0] in_path;
    integer fd, c;
    initial begin
        repeat (4) @(posedge clk);
        rst = 0;
        if ($value$plusargs("in=%s", in_path)) begin
            fd = $fopen(in_path, "rb");
            if (fd == 0) begin
                $display("tb: cannot open %0s", in_path);
                $finish(0);
            end
            c = $fgetc(fd);
            while (c != -1) begin
                send_byte(c[7:0]);
                c = $fgetc(fd);
            end
            $fclose(fd);
        end
    end

    // stdout
    reg [7:0] rx_byte;
    integer j;
    initial begin
        forever begin
            @(negedge tx);
            repeat (CLKS_PER_BIT + CLKS_PER_BIT / 2) @(posedge clk);
            for (j = 0; j < 8; j = j + 1) begin
                rx_byte[j] = tx;
                repeat (CLKS_PER_BIT) @(posedge clk);
            end
            $write("%c", rx_byte);
            $fflush;
        end
    end

    // termination
    integer cycles = 0, max_cycles = 50_000_000;
    initial begin
        if (!$value$plusargs("max_cycles=%d", max_cycles)) max_cycles = 50_000_000;
        forever begin
            @(posedge clk);
            cycles = cycles + 1;
            if (halted && dut.chip.tx.ready) begin
                // Let the last stop bit finish.
                repeat (2 * CLKS_PER_BIT) @(posedge clk);
                $finish(0);
            end
            if (cycles >= max_cycles) begin
                $display("\ntb: timeout after %0d cycles (pc=%0d)", cycles, dut.chip.cpu.pc);
                $finish(0);
            end
        end
    end
endmodule
