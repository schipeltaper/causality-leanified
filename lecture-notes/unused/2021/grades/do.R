source('round_grade.R')

A<-read.csv('grades_21503d.csv')
finalexam<-A[,16]*9/45+1
resitexam<-A[,17]*9/30+1
exercises_maxpoints<-c(7,3,14,5,9,6,6,7,7,9,4,15)
exercises<-as.matrix(A[,4:15]) / t(matrix(rep(exercises_maxpoints,dim(A)[1]),nrow=length(exercises_maxpoints)))
exercises[which(is.na(exercises))]<-0
exercises<-rowSums(exercises[,1:12])/12*9+1
finalgrade<-0.15*exercises+0.85*finalexam
resitgrade<-0.15*exercises+0.85*resitexam
#nap<-which(is.na(A[,16]))
#finalexam[nap]<-NA
#finalgrade[nap]<-NA
#nap<-which(is.na(A[,17]))
#resitexam[nap]<-NA
#resitgrade[nap]<-NA

finalgrades<-cbind(A[,1],A[,2],exercises,finalexam,finalgrade)
colnames(finalgrades)[1]<-"Student ID"
colnames(finalgrades)[2]<-"Name"
write.csv(finalgrades,file='finalgrades.csv',row.names=FALSE)
#finalpoints<-cbind(B[,1],B[,4],B[,5],B[,6],B[,7],A[,39],round_grade(finalgrade))
#finalpoints[which(finalpoints[,6] == 0),6]<-NA
#colnames(finalpoints)<-c("studentnr","exercises1","exercises2","exercises3","finalexam","eindcijfer")
#write.csv(finalpoints,file='finalpoints.csv',row.names=FALSE)

resitgrades<-cbind(A[,1],A[,2],exercises,resitexam,resitgrade)
colnames(resitgrades)[1]<-"Student ID"
colnames(resitgrades)[2]<-"Name"
write.csv(resitgrades,file='resitgrades.csv',row.names=FALSE)

pdf('grades_final_exam.pdf')
hist(finalexam,xlim=c(0,10),c(1,1.25,1.75,2.25,2.75,3.25,3.75,4.25,4.75,5.5,6.25,6.75,7.25,7.75,8.25,8.75,9.25,9.75,10),main='Histogram grades Final Exam Causality (n=21)',xlab='Grade',ylab='Density')
dev.off()

pdf('grades_exercises.pdf')
hist(exercises,xlim=c(0,10),c(1,1.25,1.75,2.25,2.75,3.25,3.75,4.25,4.75,5.5,6.25,6.75,7.25,7.75,8.25,8.75,9.25,9.75,10),main='Histogram grades Exercises Causality (n=21)',xlab='Grade',ylab='Density')
dev.off()

pdf('grades_final.pdf')
hist(finalgrade,xlim=c(0,10),c(1,1.25,1.75,2.25,2.75,3.25,3.75,4.25,4.75,5.5,6.25,6.75,7.25,7.75,8.25,8.75,9.25,9.75,10),main='Histogram grades Final Exam Causality (n=21)',xlab='Grade',ylab='Density')
dev.off()

mean(finalexam,na.rm=T)
mean(finalgrade,na.rm=T)
