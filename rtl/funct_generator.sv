/* 
	=========================================================================================
	Module name	: funct_generator
	Author		: Ana Godoy
	Email		: ana.gm@circuify.com
	Filename	: funct_generator.sv
	Type		: SystemVerilog Top
	
	Description	: Function Generator IPCore
	-----------------------------------------------------------------------------------------
	clocks	        : clk
	reset		: async posedge "rst"		
	-----------------------------------------------------------------------------------------
	Version		: 1.0
	Date		: Jun 2024
	-----------------------------------------------------------------------------------------
*/

module funct_generator #(
	parameter DATA_WIDTH = 32,
        parameter INT_BITS = 4,        
        parameter FIXED_POINT_BITS = (DATA_WIDTH - INT_BITS)
        )(
	//INPUTS
	input  logic 				                clk,
	input  logic 				                rst,
	input  logic 				                en_low_i, 
	input  logic 				                enh_conf_i, 
        input  logic signed  [INT_BITS-1 : 0]	                amp_i,  
	input  logic	     [1:0]	                        sel_i,
	//OUTPUTS
	output logic                                            wr_en_o,
	output logic signed  [INT_BITS-1 : -FIXED_POINT_BITS]   data_o
);

localparam LUT_ADDR = 8;

logic        [LUT_ADDR-1:0] addr, addr_temp;

logic        [INT_BITS-1 : -FIXED_POINT_BITS]	amp_reg;

logic signed [INT_BITS-1 : 0-FIXED_POINT_BITS] cos_temp;
logic signed [INT_BITS-1 : 0-FIXED_POINT_BITS] sin_temp;
logic signed [INT_BITS-1 : 0-FIXED_POINT_BITS] trian_temp;
logic signed [INT_BITS-1 : 0-FIXED_POINT_BITS] squa_temp;

logic signed [INT_BITS-1 : 0-FIXED_POINT_BITS] data_select;

logic signed [(DATA_WIDTH*2)-1:0] data_temp;

/************** FSM signals *****************/

bit enh_addr_fsm;
bit enh_config_fsm;
bit clrh_addr_fsm;
bit enh_gen_fsm;


bit en_config_amp;

/***********FSM*****************/
funct_generator_fsm fsm(
    .clk(clk        ),
    .rst(rst        ),
    .en_low_i(en_low_i),
    .enh_conf_i(enh_conf_i),
    .clrh_addr_fsm(clrh_addr_fsm),
    .enh_addr_fsm(enh_addr_fsm),
    .enh_config_fsm(enh_config_fsm),
    .enh_gen_fsm(enh_gen_fsm)
);
    


/***********LUT sin*****************/
funct_generator_lut #(
    .DATA_WIDTH	(DATA_WIDTH),
    .ADDR_WIDTH	(LUT_ADDR),
    .TXT_FILE	("/home/agodoy/Documents/DV/Generator_fifo_project/rtl/sin.txt")
)
LUT_sin(
    .clk	(clk    ),	
    .read_addr_i(addr   ),
    .read_data_o(sin_temp)
);

/***********LUT cos*****************/
funct_generator_lut #(
    .DATA_WIDTH	(DATA_WIDTH),
    .ADDR_WIDTH	(LUT_ADDR),
    .TXT_FILE	("/home/agodoy/Documents/DV/Generator_fifo_project/rtl/cos.txt")
)
LUT_cos(
    .clk	(clk    ),	
    .read_addr_i(addr   ),
    .read_data_o(cos_temp)
);	

/***********LUT triangular*****************/
funct_generator_lut #(
    .DATA_WIDTH	(DATA_WIDTH),
    .ADDR_WIDTH	(LUT_ADDR),
    .TXT_FILE	("/home/agodoy/Documents/DV/Generator_fifo_project/rtl/triangular.txt")
)
LUT_trian(
    .clk	(clk    ),	
    .read_addr_i(addr   ),
    .read_data_o(trian_temp)
);

/***********LUT cos*****************/
funct_generator_lut #(
    .DATA_WIDTH	(DATA_WIDTH),
    .ADDR_WIDTH	(LUT_ADDR),
    .TXT_FILE	("/home/agodoy/Documents/DV/Generator_fifo_project/rtl/square.txt")
)
LUT_squa(
    .clk	(clk    ),	
    .read_addr_i(addr   ),
    .read_data_o(squa_temp)
);	

/***********MULTIPLICACION AMPLITUD*****************/
funct_generator_multi #(
    .DATA_WIDTH(DATA_WIDTH)
)
amplitud_confi(
    .enh(!en_low_i), 
    .a_i(data_select),
    .b_i(amp_reg),
    .data_o(data_temp)
);

assign data_o = data_temp[(DATA_WIDTH*2)-INT_BITS:FIXED_POINT_BITS];

/***********ADDER ADDRES*****************/
funct_generator_adder #(
    .DATA_WIDTH	(LUT_ADDR)
)
adder_addres(
    .clrh   (clrh_addr_fsm),
    .enh    (enh_addr_fsm),
    .data_a_i(addr),
    .data_b_i(8'h1),
    .data_c_i(8'h0),
    .data_o (addr_temp) 	
);


/**********************REGISTER*****************************/

funct_generator_register #(
    .DATA_WIDTH(LUT_ADDR),
    .RESET_VALUE(0)
)
addr_reg(
    .clk	(clk	    ),
    .rst	(rst	    ),
    .clrh	(1'b0       ),
    .enh	(!en_low_i  ),
    .d  	(addr_temp  ),
    .q	        (addr       )	
);

funct_generator_register_amp #(
    .DATA_WIDTH(DATA_WIDTH),
    .RESET_VALUE(32'h10000000)
)
amp_register(
    .clk	(clk	    ),
    .rst	(rst	    ),
    .clrh	(1'b0        ),
    .enh	(en_config_amp),
    .d  	({amp_i, {FIXED_POINT_BITS{1'b0}}}),
    .q	        (amp_reg    )	
);

assign en_config_amp = (enh_config_fsm && (amp_i != 8'h0 ) && (amp_i != 4'h8)); 
/********************MULTIPLEXOR*****************************/

funct_generator_mux #(
    .DATA_WIDTH(DATA_WIDTH)
)mux_signal(
	.sel_i(sel_i), 
        .enh(enh_gen_fsm),
	.data_0_i(sin_temp),
	.data_1_i(cos_temp),
	.data_2_i(trian_temp),
	.data_3_i(squa_temp),
	.data_o(data_select)
);

assign wr_en_o = (enh_gen_fsm)? 1'b1 : 1'b0;

endmodule
