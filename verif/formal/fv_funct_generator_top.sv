import gen_fifo_defines_pkg::*;

module fv_generator(
	input  logic 				     	clk,
	input  logic 				     	rst,
	input  logic 				       	en_low_i, 
	input  logic 				       	enh_conf_i, 
        input  logic signed  [`INT_BITS-1 : 0]	    	amp_i,  
	input  logic	     [1:0]	                sel_i,
	input logic                                	wr_en_o,
  	input logic signed  [`DATA_WIDTH-1 : 0]  	data_o,
	logic        [`LUT_ADDR-1:0] 			addr, addr_temp,
	logic        [`DATA_WIDTH-1 : 0]		amp_reg,
	logic signed [`DATA_WIDTH-1 : 0] 		cos_temp,
	logic signed [`DATA_WIDTH-1 : 0] 		sin_temp,
	logic signed [`DATA_WIDTH-1 : 0] 		trian_temp,
	logic signed [`DATA_WIDTH-1 : 0] 		squa_temp,
	logic signed [`DATA_WIDTH-1 : 0] 		data_select,
	logic signed [(`DATA_WIDTH*2)-1:0] 		data_temp,
	bit enh_config_fsm,
	bit clrh_addr_fsm,
	bit enh_gen_fsm,
	bit en_config_amp
     );
	bit flag;
   	reg [`DATA_WIDTH-1:0] expected_sin [2**`LUT_ADDR-1:0];
    	reg [`DATA_WIDTH-1:0] expected_cos [2**`LUT_ADDR-1:0];
    	reg [`DATA_WIDTH-1:0] expected_trian [2**`LUT_ADDR-1:0];
    	reg [`DATA_WIDTH-1:0] expected_squa [2**`LUT_ADDR-1:0];

  	initial begin
        	$readmemh(SIN_FILE, expected_sin);
        	$readmemh(COS_FILE, expected_cos);
        	$readmemh(TRIAN_FILE, expected_trian);
        	$readmemh(SQUA_FILE, expected_squa);
    	end
	
	always @(posedge clk) begin
      		if (rst == 1'b1)
        		flag <= 1'b0;
      		else 
        		flag <=1'b1;
 	end

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ funct_generator_adder ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━//

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) Assume enable and clear signals are not active simultaneously.
	enh_and_clrh_notactive_same: assume property (@(posedge clk) disable iff (rst) !(enh_gen_fsm && clrh_addr_fsm));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 2) The property assures that when clrh is high, the output addr_temp is set to zero.
	clrh_on_addr_temp_zero: assert property (@(posedge clk) disable iff (rst) (clrh_addr_fsm) |-> (addr_temp == 0)) $info("Assetion pass clrh_on_data_o_zero");
	else $error(" Asserion fail clrh_on_data_o_zero");
	
	// 3) The property assures that when enh is low and clrh is low, the output addr_temp remains unchanged. //changing |=> for |-> and adding a flag
	addr_temp_stability_when_disabled: assert property (@(posedge clk) disable iff (rst) (!enh_gen_fsm && !clrh_addr_fsm && flag) |-> ($stable(addr_temp)))
	$info("Assetion pass data_o_stability_when_disabled"); else $error(" Asserion fail data_o_stability_when_disabled");
	
	// 4) The property assures that when enh is active the adder adds 1 to the current addess to produce the next addess when enh is high. //adding the modulo operation for the wrapping behavior
	addr_increment1_when_enh: assert property (@(posedge clk) disable iff (rst) (enh_gen_fsm && !clrh_addr_fsm) |-> (addr_temp == (addr + 1) % 256))
	$info("Assetion pass addr_increment1_when_enh"); else $error(" Asserion fail addr_increment1_when_enh");

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 5) Cover that is addr_temp is 0 when clrh is asserted.
	clrh_clears_addr_temp: cover property (@(posedge clk) disable iff (rst) (clrh_addr_fsm && (addr_temp == 0)));
	
	// 6) Cover the scenario where enh is high, clrh is low, and addr_temp is addr + 1. 
	next_address_is_addr_plus_1: cover property (@(posedge clk) disable iff (rst) (enh_gen_fsm && !clrh_addr_fsm && (addr_temp == addr + 1)));

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ funct_generator_multi ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━//

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) 

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures when enh_gen_fsm is active the multiplication operation performs correcty.
	multiplication_correct_when_enh_gen_fsm: assert property (@(posedge clk) disable iff (rst) (enh_gen_fsm) |-> (data_temp == (data_select * amp_reg))) $info("Assetion pass clrh_on_data_o_zero");
	else $error(" Asserion fail clrh_on_data_o_zero");

	// 2) The property assures that when a reset happen data_o will be assigned the value '0.
	data_o_0_when_rst: assert property (@(posedge clk) disable iff (rst) (!flag) |-> (data_temp == '0)) $info("Assetion pass clrh_on_data_o_zero");
	else $error(" Asserion fail clrh_on_data_o_zero");

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 3) Cover property for the multiplication scenario.
	cover_multiplication_when_enh_gen_fsm: cover property (@(posedge clk) disable iff (rst) ((enh_gen_fsm) && (data_temp == (data_select * amp_reg))));

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ funct_generator_fsm ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━//
///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) 

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////
	
      	// 1)The property assures that when rst enh_config_fsm is 0. //changing |=> for |-> operator and !flag
      	enh_config_fsm_0_when_rst: assert property (@(posedge clk) disable iff (rst) (!flag) |->  enh_config_fsm == 1'b0) $info("Assetion pass enh_config_fsm_0_when_rst");
	else $error(" Asserion fail enh_config_fsm_0_when_rst");
            
   	// 2) The property assures that when rst enh_gen_fsm is 0. //changing |=> for |-> operator and !flag
      	enh_gen_fsm_0_when_rst: assert property (@(posedge clk) disable iff (rst) (!flag) |->  enh_gen_fsm == 1'b0) $info("Assetion pass enh_gen_fsm_0_when_rst");
      	else $error(" Asserion fail enh_gen_fsm_0_when_rst");
            
	// 3) The property assures that when rst clrh_addr_fsm is 0.//changing |=> for |-> operator and !flag
        clrh_addr_fsm_0_when_rst: assert property (@(posedge clk) disable iff (rst) (!flag) |->  clrh_addr_fsm == 1'b0) $info("Assetion pass clrh_addr_fsm_0_when_rst");
	else $error(" Asserion fail clrh_addr_fsm_0_when_rst");
      
 	//  4) The property assures GEN to CONFI transition.
	assert_gen_to_confi: assert property (@(posedge clk) disable iff (rst) (enh_gen_fsm && enh_conf_i) |=> (enh_config_fsm)) $info("Assetion pass assert_gen_to_confi");
	//else $error(" Asserion fail assert_gen_to_confi");

	// 5) The property assures CONFI to GEN transition  // was added (!enh_conf_i) 
  	assert_confi_to_gen: assert property (@(posedge clk) disable iff (rst) (enh_config_fsm && (!en_low_i) && (!enh_conf_i) ) |=> (enh_gen_fsm)) $info("Assetion pass assert_confi_to_gen");
	else $error(" Asserion fail assert_confi_to_gen");
        
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   
  	// 6) Cover that clrh_addr_fsm signal is asserted.
	cover_clrh_addr_fsm: cover property (@(posedge clk) disable iff (rst) clrh_addr_fsm);
 	
	// 7) Cover that enh_config_fsm signal is asserted.
	cover_enh_config_fsm: cover property (@(posedge clk) disable iff (rst) enh_config_fsm);
 	
     	// 8) Cover that  enh_gen_fsm signal is asserted.
	cover_enh_gen_fsm: cover property (@(posedge clk) disable iff (rst) enh_gen_fsm);
      
  	// 9) Cover that  en_low_i signal is asserted.
   	cover_en_low_i: cover property (@(posedge clk) disable iff (rst) en_low_i);
    
  	// 10) Cover that  enh_conf_i signal is asserted.
	cover_enh_conf_i: cover property (@(posedge clk) disable iff (rst) enh_conf_i);

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ funct_generator_lut ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━//

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) 

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////
	
	// 1) The property assures sin_temp has a valid value.
	sin_temp_valid_data: assert property (@(posedge clk) disable iff (rst) !$isunknown(sin_temp)) $info("Assetion pass sin_temp_valid_data");
	else $error(" Asserion failsin_temp_valid_data");

      	// 2) The property assures cos_temp has a valid value.
	cos_temp_valid_data: assert property (@(posedge clk) disable iff (rst) !$isunknown(cos_temp)) $info("Assetion pass cos_temp_valid_data");
      	else $error(" Asserion fail cos_temp_valid_data");

      	// 3) The property assures trian_temp has a valid value.
	trian_temp_valid_data: assert property (@(posedge clk) disable iff (rst) !$isunknown(trian_temp)) $info("Assetion pass trian_temp_valid_data");
	else $error(" Asserion failtrian_temp_valid_data");

	// 4) The property assures squa_temp has a valid value.
	squa_temp_valid_data: assert property (@(posedge clk) disable iff (rst) !$isunknown(squa_temp)) $info("Assetion pass squa_temp_valid_data");
	else $error(" Asserion fail squa_temp_valid_data");
   
      	// 5) The property assures the values in the sin.txt are the same as sin_temp
	expected_sin_equal_sin_temp: assert property (@(posedge clk) flag |=> (sin_temp == expected_sin[$past(addr)]))$info("Assetion pass expected_sin_equal_sin_temp");
        else $error(" Asserion fail at addrs: %0d, in temp: %0h, in expect: %0h", addr,sin_temp, expected_sin[addr]);
        
	// 6) The property assures the values in the cos.txt are the same as cos_temp
	expected_cos_equal_cos_temp: assert property (@(posedge clk)flag |=>(cos_temp ==  expected_cos[$past(addr)]))$info("Assetion pass expected_cos_equal_cos_temp");
        else $error("Asserion fail at addrs: %0d, in temp: %0h, in expect: %0h", addr,cos_temp, expected_sin[addr]);
       	
	// 7) The property assures the values in the trian.txt are the same as trian_temp
	expected_trian_equal_trian_temp: assert property (@(posedge clk)flag |=>(trian_temp ==  expected_trian[$past(addr)]))$info("Assetion expected_trian_equal_trian_temp");
        else $error(" Asserion fail at addr: %0d, in temp: %0h, in expect: %0h", addr,trian_temp, expected_sin[addr]);
        
	// 8) The property assures the values in the squa.txt are the same as squa_temp
	expected_squa_equal_squa_temp: assert property (@(posedge clk) flag |=>(squa_temp ==  expected_squa[$past(addr)]))$info("expected_squa_equal_squa_temp");
	else $error(" Asserion fail at addrs: %0d, in temp: %0h, in expect: %0h", addr,squa_temp, expected_sin[addr]);

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
     	// 9) Covers when addr reaches max value.
	cover_sin_max_addr: cover property (@(posedge clk) disable iff (rst) addr == ((2**`LUT_ADDR) - 1));

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ funct_generator_mux ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━//

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) 

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures data_select matches sin_temp when sel_i is 0 and enh is active.
	data_select_is_sin_temp: assert property (@(posedge clk) ( sel_i == 2'b00) |-> data_select == sin_temp) $info("Assetion pass data_select_is_sin_temp");
	else $error(" Asserion fail data_select_is_sin_temp");
	
	// 2) The property assures data_selectmatches cos_temp when sel_i is 1 and enh is active.
	data_select_is_cos_temp: assert property (@(posedge clk) (sel_i == 2'b01) |-> data_select== cos_temp) $info("Assetion pass data_select_is_cos_temp");
	else $error(" Asserion fail data_select_is_cos_temp");

	// 3) The property assures data_select matches trian_temp when sel_i is 2 and enh is active.
	data_select_is_trian_temp: assert property (@(posedge clk) (sel_i == 2'b10) |-> data_select == trian_temp) $info("Assetion pass data_select_is_trian_temp");
	else $error(" Asserion fail data_select_is_trian_temp");

	// 4) The property assures data_select matches squa_temp when sel_i is 3 and enh is active.
	data_select_is_squa_temp: assert property (@(posedge clk) (sel_i == 2'b11) |-> data_select == squa_temp) $info("Assetion pass data_select_is_squa_temp");
	else $error(" Asserion fail data_select_is_squa_temp");

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 1) 

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ funct_generator_register ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━//

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) 

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures that when rst is active, addr should be RESET_VALUE.
  	when_rst_addr_is_reset_value: assert property (@(posedge clk) (!flag) |-> (addr == `RESET_VALUE)) $info("Assetion pass when_rst_addr_is_reset_value");
	else $error(" Asserion fail when_rst_addr_is_reset_value");

	// 2) The property assures that when enh_gen_fsm is active, addr should be equal to addr_temp.
      	when_enh_gen_fsm_1_addr: assert property (@(posedge clk) enh_gen_fsm |=> (addr == $past(addr_temp))) $info("Assetion pass when_enh_gen_fsm_1_addr");
	else $error(" Asserion fail when_enh_gen_fsm_1_addr");

	// 3) The property assures that if enh_gen_fsm is not active, addr does not change.
	enh_gen_fsm_0_addr_stable: assume property (@(posedge clk) disable iff (rst) (!enh_gen_fsm) |=> (addr == $past(addr))) $info("Assetion pass enh_gen_fsm_0_addr_stable");
	else $error(" Asserion fail enh_gen_fsm_0_addr_stable");

	// 4) The property assures that when rst is active, amp_reg should be RESET_AMP.
  	when_rst_amp_reg_is_reset_amp: assert property (@(posedge clk) (!flag) |-> (amp_reg == `RESET_AMP)) $info("Assetion pass when_rst_amp_reg_is_reset_amp");
	else $error(" Asserion fail when_rst_amp_reg_is_reset_amp");

	// 5)The property assures that amp_reg holds the correct value based on en_config_amp.
	when_en_config_amp_1_amp_reg : assert property (@(posedge clk) disable iff (rst) en_config_amp |=> (amp_reg == $past({amp_i, {(`DATA_WIDTH - `INT_BITS){1'b0}}}))) $info("Assetion pass when_en_config_amp_1_amp_reg");
	else $error(" Asserion fail when_en_config_amp_1_amp_reg");

	// 6)The property assures that if en_config_amp is not active, amp_reg does not change.
	en_config_amp_0_amp_reg_stable: assume property (@(posedge clk) disable iff (rst) (!en_config_amp) |=> (amp_reg == $past(amp_reg))) $info("Assetion pass en_config_amp_0_amp_reg_stable");
	else $error(" Asserion fail en_config_amp_0_amp_reg_stable");

 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 1)
	
endmodule
/*☆✼★☆✼★━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━★✼☆☆✼★｡
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━*/


bind funct_generator fv_funct_generator_top fv_funct_generator_top_inst(.*); 

