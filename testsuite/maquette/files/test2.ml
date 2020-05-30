class reload = object (self)

inherit Reloadgen.reload_generic as super ;

method reload_operation op arg res = () ;

method reload_test tst arg = () ;

initializer f x ;

end
    ;
    
