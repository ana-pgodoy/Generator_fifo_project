/* 
	=========================================================================================
	Module name	: tb
	Author		: Godoy Monroy Ana Paula
	Email		: anna.pgm28@gmail.com
	Filename	: tb.sv
	Type		: SystemVerilog Top
	
	Description	: Test Bench para funct_generator
        -----------------------------------------------------------------------------------------
	clocks	        : clk
	reset		: async posedge "rst"		
	-----------------------------------------------------------------------------------------
	Version		: 1.0
	Date		: Jun 2024
	-----------------------------------------------------------------------------------------
*/
import gen_fifo_defines_pkg::*;

module tb();


    localparam PERIOD = 10ns;
    localparam MID_PERIOD = (PERIOD/2);

    bit clk; 
    bit rst; 	
    bit en_low_i;	
    bit	enh_conf_i;
    logic signed  [`INT_BITS-1:0] amp_i;	
    bit [1:0] sel_i;
    //OUTPUTS
    bit wr_en_o;
    logic signed  [`DATA_WIDTH-1 : 0]  data_o;

        
    funct_generator#(
	.DATA_WIDTH(`DATA_WIDTH),
        .INT_BITS(`INT_BITS),        
        .LUT_ADDR(`LUT_ADDR),
        .RESET_VALUE(`RESET_VALUE),
        .RESET_AMP(`RESET_AMP),
        .COS_FILE(`COS_FILE),
        .SIN_FILE(`SIN_FILE),
        .TRIAN_FILE(`TRIAN_FILE),
        .SQUA_FILE(`SQUA_FILE)
    )DUT(
	.clk(clk),
	.rst(rst),
	.en_low_i(en_low_i), 
	.enh_conf_i(enh_conf_i),
	.amp_i(amp_i), 
        .sel_i(sel_i),
	.wr_en_o(wr_en_o),
	.data_o(data_o)
    );

    //clock source
     always clk = #(MID_PERIOD) ~clk;

    
    initial begin
	rst <= 1'b1;   
	en_low_i <= 1'b1;
        amp_i <= 4'h8;
        enh_conf_i <= 1'b0;
        sel_i <= 2'b00;
	#20;
	rst <= 1'b0;
	#20;
        en_low_i <= 1'b0;

        #2540;
        enh_conf_i <= 1'b1;	
        #40;
        enh_conf_i <= 1'b0;	
        #2540;
        
        amp_i <= 4'h8;
        sel_i <= 2'b01;
        #2540;
        enh_conf_i <= 1'b1;	
        #40;
        enh_conf_i <= 1'b0;	
        #2540;
        
        amp_i <= 4'h2;
        sel_i <= 2'b10; 
        #2540;
        enh_conf_i <= 1'b1;	
        #40;
        enh_conf_i <= 1'b0;	
        #2540;

        amp_i <= 4'h0;
        sel_i <= 2'b11;
        #2540;
        enh_conf_i <= 1'b1;	
        #40;
        enh_conf_i <= 1'b0;	
        #2540;
        en_low_i <= 1'b1;
        #500;
        en_low_i <= 1'b0;
        #500;
	
	$finish;	
    end

    //Simulation setting	
    initial begin
	$timeformat(-9, 2, "ns", 20);
        $dumpfile("gen_fifo.vcd"); $dumpvars;
    end
endmodule
