#include <iostream>
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"

#include "llvm/Support/raw_ostream.h"
#include "clang/Sema/Sema.h"
#include "clang/AST/RecursiveASTVisitor.h"

#include "clang/Basic/Diagnostic.h"

#include "clang/AST/DeclObjC.h"

using namespace clang;
using namespace std;
using namespace llvm;
using namespace clang::ast_matchers;


namespace CodeStandardsPlugin {
    
    // MARK: - my handler
    class CodeStandardsHandler : public MatchFinder::MatchCallback {
    private:
        CompilerInstance &ci;
    public:
        CodeStandardsHandler(CompilerInstance &ci) :ci(ci) {}
        
        //检测类名
        void checkInterfaceDecl(const ObjCInterfaceDecl *decl)
        {
            StringRef className = decl->getName();
            
            //判断首字母不能以小写开头
            char c = className[0];
            if (isLowercase(c)) {
                std::string tempName = decl->getNameAsString();
                tempName[0] = toUppercase(c);
                StringRef replacement(tempName);
                SourceLocation nameStart = decl->getLocation();
                SourceLocation nameEnd = nameStart.getLocWithOffset(className.size() - 1);
                FixItHint fixItHint = FixItHint::CreateReplacement(SourceRange(nameStart, nameEnd), replacement);
                
                //报告警告
                SourceLocation location = decl->getLocation();
                diagWaringReport(location, "类名不能以小写字母开头", &fixItHint);
            }
            
            //判断下划线不能在类名有没有包含下划线
            size_t pos = decl->getName().find('_');
            if (pos != StringRef::npos) {
                std::string tempName = decl->getNameAsString();
                std::string::iterator end_pos = std::remove(tempName.begin(), tempName.end(), '_');
                tempName.erase(end_pos, tempName.end());
                StringRef replacement(tempName);
                SourceLocation nameStart = decl->getLocation();
                SourceLocation nameEnd = nameStart.getLocWithOffset(className.size() - 1);
                FixItHint fixItHint = FixItHint::CreateReplacement(SourceRange(nameStart, nameEnd), replacement);
                
                //报告警告
                SourceLocation loc = decl->getLocation().getLocWithOffset(pos);
                diagWaringReport(loc, "类名中不能带有下划线", &fixItHint);
            }
        }
        
        //检测属性
        void checkPropertyDecl(const clang::ObjCPropertyDecl *propertyDecl)
        {
            
            StringRef name = propertyDecl -> getName();
            //名称必须以小写字母开头
            bool checkUppercaseNameIndex = 0;
            if (name.find('_') == 0)
            {
                //以下划线开头则首字母位置变为1
                checkUppercaseNameIndex = 1;
            }
            char c = name[checkUppercaseNameIndex];
            if (isUppercase(c))
            {
                //修正提示
                std::string tempName = name.str();
                tempName[checkUppercaseNameIndex] = toLowercase(c);
                StringRef replacement(tempName);
                SourceLocation nameStart = propertyDecl->getLocation();
                SourceLocation nameEnd = nameStart.getLocWithOffset(name.size() - 1);
                FixItHint fixItHint = FixItHint::CreateReplacement(SourceRange(nameStart, nameEnd), replacement);
                SourceLocation location = propertyDecl->getLocation();
                //报告警告
                diagWaringReport(location, "属性名称必须以小写字母开头", &fixItHint);
            }
            
            // 检测属性
            if (propertyDecl->getTypeSourceInfo()) {
                
                ObjCPropertyAttribute::Kind attrKind = propertyDecl->getPropertyAttributes();
                SourceLocation location = propertyDecl->getLocation();
                string typeStr = propertyDecl->getType().getAsString();
                
                //判断string需要使用copy
                if ((typeStr.find("NSString")!=string::npos)&& !(attrKind & ObjCPropertyAttribute::Kind::kind_copy)) {
                    diagWaringReport(location, "NSString 建议使用 copy 代替 strong.", NULL);
                }
               
                //判断int需要使用NSInteger
                if(!typeStr.compare("int")){
                    diagWaringReport(location, "建议使用 NSInteger 替换 int.", NULL);
                }
                //判断delegat使用weak
                if ((typeStr.find("<")!=string::npos && typeStr.find(">")!=string::npos) && (typeStr.find("Array")==string::npos) && !(attrKind & ObjCPropertyAttribute::Kind::kind_weak)) {
                    diagWaringReport(location, "建议使用 weak 定义 Delegate.", NULL);
                }
            }
        }
        
        //检测方法
        void checkMethodDecl(const clang::ObjCMethodDecl *methodDecl) {
            
            //检查名称的每部分，都不允许以大写字母开头
            Selector sel = methodDecl -> getSelector();
            int selectorPartCount = methodDecl -> getNumSelectorLocs();
            for (int i = 0; i < selectorPartCount; i++)
            {
                 StringRef selName = sel.getNameForSlot(i);
                 char c = selName[0];
                 if (isUppercase(c))
                 {
                     //修正提示
                     std::string tempName = selName.str();
                     tempName[0] = toLowercase(c);
                     StringRef replacement(tempName);
                     SourceLocation nameStart = methodDecl -> getSelectorLoc(i);
                     SourceLocation nameEnd = nameStart.getLocWithOffset(selName.size() - 1);
                     FixItHint fixItHint = FixItHint::CreateReplacement(SourceRange(nameStart, nameEnd), replacement);
                          
                     //报告警告
                     SourceLocation location = methodDecl->getLocation();
                     diagWaringReport(location, "方法名要以小写开头", &fixItHint);
                 }
            }
            
            //检测方法中定义的参数名称是否存在大写开头
            for (ObjCMethodDecl::param_const_iterator it = methodDecl->param_begin(); it != methodDecl->param_end(); it++)
            {
                const ParmVarDecl *parmVarDecl = *it;
                StringRef name = parmVarDecl -> getName();
                char c = name[0];
                if (isUppercase(c))
                {
                    //修正提示
                    std::string tempName = name.str();
                    tempName[0] = toLowercase(c);
                    StringRef replacement(tempName);
                    SourceLocation nameStart = parmVarDecl -> getLocation();
                    SourceLocation nameEnd = nameStart.getLocWithOffset(name.size() - 1);
                    FixItHint fixItHint = FixItHint::CreateReplacement(SourceRange(nameStart, nameEnd), replacement);
                        
                    //报告警告
                    SourceLocation location = methodDecl->getLocation();
                    diagWaringReport(location, "参数名称要小写开头", &fixItHint);
                }
            }
        }
        
        
        template <unsigned N>
        void diagWaringReport(SourceLocation Loc, const char (&FormatString)[N], FixItHint *Hint)
        {
            DiagnosticsEngine &diagEngine = ci.getDiagnostics();
            unsigned DiagID = diagEngine.getCustomDiagID(clang::DiagnosticsEngine::Warning, FormatString);
            (Hint!=NULL) ? diagEngine.Report(Loc, DiagID) << *Hint : diagEngine.Report(Loc, DiagID);
        }
        
        void run(const MatchFinder::MatchResult &Result) {

            if (const ObjCInterfaceDecl *interfaceDecl = Result.Nodes.getNodeAs<ObjCInterfaceDecl>("ObjCInterfaceDecl")) {
                string filename = ci.getSourceManager().getFilename(interfaceDecl->getSourceRange().getBegin()).str();
                if(isUserSourceCode(filename))
                {
                    std::string tempName = interfaceDecl->getNameAsString();
                    cout << "ObjCInterfaceDecl" + tempName << endl;
                    //类的检测
                    checkInterfaceDecl(interfaceDecl);
                }
            }

            if (const ObjCPropertyDecl *propertyDecl = Result.Nodes.getNodeAs<ObjCPropertyDecl>("ObjcPropertyDecl")) {
                string filename = ci.getSourceManager().getFilename(propertyDecl->getSourceRange().getBegin()).str();
                if(isUserSourceCode(filename))
                {
                    std::string tempName = propertyDecl->getNameAsString();
                    cout << "ObjcPropertyDecl" + tempName << endl;
                    //属性的检测
                    checkPropertyDecl(propertyDecl);
                }
            }

            if (const ObjCMethodDecl *methodDecl = Result.Nodes.getNodeAs<ObjCMethodDecl>("ObjCMethodDecl")) {
                string filename = ci.getSourceManager().getFilename(methodDecl->getSourceRange().getBegin()).str();
                if(isUserSourceCode(filename))
                {
                    std::string tempName = methodDecl->getNameAsString();
                    cout << "ObjcMethodDecl" + tempName << endl;
                    //方法的检测
                    checkMethodDecl(methodDecl);
                }
            }
        }
        
        /**
          判断是否为用户源码

          @param decl 声明
          @return true 为用户源码，false 非用户源码
         */
        bool isUserSourceCode (string filename)
        {
            if (filename.empty())
                return false;
            
              //非XCode中的源码都认为是用户源码
            if(filename.find("/Applications/Xcode.app/") == 0)
                return false;
                    
            return true;
        }
        
    };
    
    class CodeStandardsASTConsumer: public ASTConsumer {
    private:
        MatchFinder matcher;
        CodeStandardsHandler handler;
    public:
        //调用CreateASTConsumer方法后就会加载Consumer里面的方法
        CodeStandardsASTConsumer(CompilerInstance &ci) :handler(ci) {
            matcher.addMatcher(objcInterfaceDecl().bind("ObjCInterfaceDecl"), &handler);
            matcher.addMatcher(objcMethodDecl().bind("ObjCMethodDecl"), &handler);
            matcher.addMatcher(objcPropertyDecl().bind("ObjcPropertyDecl"), &handler);
        }
        
        //遍历完一次语法树就会调用一次下面方法
        void HandleTranslationUnit(ASTContext &context) {
            matcher.matchAST(context);
        }
    };
    
    class CodeStandardsASTAction: public PluginASTAction {
        std::set<std::string> ParsedTemplates;
    public:
        unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &ci, StringRef iFile) {
            return unique_ptr<CodeStandardsASTConsumer> (new CodeStandardsASTConsumer(ci));
        }
        
        bool ParseArgs(const CompilerInstance &ci, const std::vector<std::string> &args) {
            return true;
        }
    };
}



static FrontendPluginRegistry::Add<CodeStandardsPlugin::CodeStandardsASTAction>
X("CodeStandardsPlugin", "CodeStandardsPlugin 代码规范检查");


