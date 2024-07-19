import gen_fifo_defines_pkg::*;

module fv_funct_generator_fsm_i (
  	input logic clk,
  	input logic rst,
  	input logic enh_conf_i,
  	input logic en_low_i,
    	input logic clrh_addr_fsm,	
    	input logic enh_config_fsm,
    	input logic enh_gen_fsm,
  	input logic [1:0] state,
  	input logic [1:0] next
);

	typedef enum logic  [1:0] {IDLE, CONFI, GEN, XX='x} state_t;
	state_t state_f, next_f;
 	
    	always_comb begin
        	case(state) 
            	0: state_f = IDLE;
            	1: state_f = CONFI;
            	2: state_f = GEN;
            	3: state_f = XX;
        	endcase
    	end

    	always_comb begin
        	case(next) 
          	0: next_f = IDLE;
            	1: next_f = CONFI;
            	2: next_f = GEN;
            	3: next_f = XX;
        	endcase
    	end
         
///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) Assumption that the initial state is IDLE.
	//initial_state_is_idle: assume property (@(posedge clk) disable iff (rst) (state == IDLE));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////
		
	// 1) This property assures state transition from IDLE to CONFIG when enh_conf_i is asserted.
	whenidle_next_config: assert property (@(posedge clk) disable iff (rst) (state_f == IDLE && enh_conf_i) |-> (next_f == CONFI))  $info("Assetion pass whenidle_next_config");
	else $error(" Asserion fail whenidle_next_config");
	
	// 2) This property assures state transition from IDLE to GEN when enh_conf_i and en_low_i are not active.
	whenidle_next_gen: assert property (@(posedge clk) disable iff (rst) ((state_f == IDLE) && ((!enh_conf_i) && (!en_low_i))) |-> (next_f == GEN))  $info("Assetion pass whenidle_next_gen");
	else $error(" Asserion fail whenidle_next_gen");
	
	// 3)	This property assures IDLE state is stable if  enh_conf_i and en_low_i are not asserted or if a rst is active.
	idle_stable: assert property (@(posedge clk) disable iff (rst) ((state_f == IDLE) && (((!enh_conf_i) && en_low_i) || rst)) |-> (next_f == IDLE))  $info("Assetion pass idle_stable");
	else $error(" Asserion fail idle_stable");

	// 4)	This property assures state transition from CONFIG to GEN when enh_conf_i and en_low_i are not active.
	whenconfig_next_gen: assert property (@(posedge clk) disable iff (rst) (state_f == CONFI && (!enh_conf_i) && (!en_low_i)) |-> (next_f == GEN))  $info("Assetion pass whenconfig_next_gen");
	else $error(" Asserion fail whenconfig_next_gen");

	// 5)	This property assures state transition from CONFIG to IDLE when enh_conf_i and en_low_i are not asserted 
	whenconfig_next_idle: assert property (@(posedge clk) disable iff (rst) (state_f == CONFI && (!enh_conf_i) && en_low_i) |-> (next_f == IDLE))  $info("Assetion pass whenconfig_next_idle");
	else $error(" Asserion fail whenconfig_next_idle");

	// 6)	This property assures state transition from GEN to CONFI when enh_conf_i is asserted.
	whengen_next_confi: assert property (@(posedge clk) disable iff (rst) (state_f == GEN && enh_conf_i) |-> (next_f == CONFI))  $info("Assetion pass whengen_next_confi");
	else $error(" Asserion fail whengen_next_confi");

	// 7)	This property assures state transition from GEN to IDLE when enh_conf_i and en_low_i are not asserted.
	whengen_next_idle: assert property (@(posedge clk) disable iff (rst) (state_f == GEN && (!enh_conf_i) && en_low_i) |-> (next_f == IDLE) )  $info("Assetion pass whengen_next_idle");
	else $error(" Asserion fail whengen_next_idle");

	// 8) This property assures clrh_addr_fsm should be high in IDLE or CONFI states //changing |=> for |-> operator
	clrh_addr_fsm_when_idle_or_confi: assert property (@(posedge clk) disable iff (rst) (state == IDLE || state == CONFI) |-> clrh_addr_fsm) $info("Assetion pass clrh_addr_fsm_when_idle_or_confi");
	else $error(" Asserion fail clrh_addr_fsm_when_idle_or_confi");

	// 9) This property assures enh_config_fsm should be high in CONFI state //changing |=> for |-> operator
	 enh_config_fsm_active_when_confi: assert property (@(posedge clk) disable iff (rst) (state == CONFI) |-> enh_config_fsm) $info("Assetion pass  enh_config_fsm_active_when_confi");
	else $error(" Asserion fail  enh_config_fsm_active_when_confi");

	// 10) This property assures enh_gen_fsm should be high in GEN state //changing |=> for |-> operator
	 enh_gen_fsm_active_when_gen: assert property (@(posedge clk) disable iff (rst) (state == GEN) |-> enh_gen_fsm) $info("Assetion pass  enh_gen_fsm_active_when_gen");
	else $error(" Asserion fail  enh_gen_fsm_active_when_gen");

///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   
  	// 1) IDLE state ocurred
    	state_idle_cover : cover property (@(posedge clk) (state_f == IDLE));

    	// 2) CONFI state ocurred
    	state_confi_cover : cover property (@(posedge clk) (state_f == CONFI));

   	 // 3) GEN state ocurred
    	state_gen_cover : cover property (@(posedge clk) (state_f == GEN));
  	
	 // 4) clrh_addr_fsm signal is asserted.
	cover_clrh_addr_fsm: cover property (@(posedge clk) disable iff (rst) clrh_addr_fsm);
 	
	// 5) enh_config_fsm signal is asserted.
	cover_enh_config_fsm: cover property (@(posedge clk) disable iff (rst) enh_config_fsm);
 	
	// 6) enh_gen_fsm: signal is asserted.
	cover_enh_gen_fsm: cover property (@(posedge clk) disable iff (rst) enh_gen_fsm);

endmodule

bind funct_generator_fsm fv_funct_generator_fsm_i fv_generator_fsm_i_inst(.*);
