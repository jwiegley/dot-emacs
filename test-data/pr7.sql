create or replace package my_package authid current_user
    -- Author  : me
    -- Date    : 06/05/2017
    -- Version : 715.00.0001
    -- Object  : sample package
    -- ----------------------------------------------------------------------------

    -------------------------------------------------------------------------------
    -- NAME    : simple_boolean_fct_1
    -- CREATED : 06/05/2017
    -- AUTHOR  : 
    -------------------------------------------------------------------------------
    -- RET  : true if all goes well, false instead
    -------------------------------------------------------------------------------
    -- DESC : dummy function
    -------------------------------------------------------------------------------
    --
    FUNCTION simple_boolean_fct_1(param1 in boolean)
    RETURN   BOOLEAN;

    -------------------------------------------------------------------------------
    -- NAME    : simple_boolean_fct_2
    -- CREATED : 06/05/2017
    -- AUTHOR  : 
    -------------------------------------------------------------------------------
    -- RET  : true if all goes well, false instead
    -------------------------------------------------------------------------------
    -- DESC : dummy function
    -------------------------------------------------------------------------------
    FUNCTION simple_bolean_fct_2(param1 in boolean)
    RETURN   BOOLEAN;

    -------------------------------------------------------------------------------
    -- NAME    : simple_boolean_fct_3
    -- CREATED : 06/05/2017
    -- AUTHOR  : 
    -------------------------------------------------------------------------------
    -- RET  : true if all goes well, false instead
    -------------------------------------------------------------------------------
    -- DESC : dummy function
    -------------------------------------------------------------------------------
    FUNCTION simple_boolean_fct_3(param1 in boolean)
    RETURN   BOOLEAN;
end my_package;
-- Local Variables:
-- sql-product: oracle
-- End:
